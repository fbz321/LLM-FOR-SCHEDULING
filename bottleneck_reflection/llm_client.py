"""LLM API client for bottleneck reflection system.

Supports Claude API (via anthropic SDK) and OpenAI-compatible APIs.
Uses the Claude Agent SDK environment if available.
"""

import os
import re
import json
import time
from typing import Optional


def build_deepseek_payload(model: str, messages: list, max_tokens: int,
                           temperature: float) -> dict:
    """Build the DeepSeek chat-completions request body.

    deepseek-reasoner is a reasoning model: it must not receive `temperature`
    or `thinking`. v4 models disable thinking; chat keeps temperature only.
    """
    payload = {
        "model": model,
        "messages": messages,
        "max_tokens": max_tokens,
    }
    if "reasoner" not in model:
        payload["temperature"] = temperature
    if "v4" in model:
        payload["thinking"] = {"type": "disabled"}
    return payload


class LLMClient:
    """Client for calling LLM APIs to generate Lean proofs."""

    def __init__(
        self,
        provider: str = "claude",
        model: str = "claude-sonnet-5",
        max_tokens: int = 4096,
        temperature: float = 0.3,
        api_key: Optional[str] = None,
    ):
        self.provider = provider
        self.model = model
        self.max_tokens = max_tokens
        self.temperature = temperature
        self.api_key = api_key or os.environ.get("ANTHROPIC_API_KEY")
        self._retry_count = 3
        self._retry_delay = 5  # seconds

    def generate(self, messages: list[dict]) -> str:
        """
        Generate a completion from the LLM.

        messages format: [{"role": "system"|"user"|"assistant", "content": "..."}]

        Returns the generated text (expected to be Lean code).
        """
        for attempt in range(self._retry_count):
            try:
                result = self._call_api(messages)
                # Strip markdown code fences if present
                result = self._clean_output(result)
                return result
            except Exception as e:
                if attempt < self._retry_count - 1:
                    print(f"  LLM API error (attempt {attempt + 1}/{self._retry_count}): {e}")
                    time.sleep(self._retry_delay * (attempt + 1))
                else:
                    raise RuntimeError(f"LLM API failed after {self._retry_count} attempts: {e}")

        return ""  # unreachable

    def _call_api(self, messages: list[dict]) -> str:
        """Call the appropriate API based on provider."""

        if self.provider == "claude":
            return self._call_claude_sdk(messages)
        elif self.provider == "claude_sdk":
            return self._call_claude_sdk(messages)
        elif self.provider == "openai":
            return self._call_openai_api(messages)
        elif self.provider == "deepseek":
            return self._call_deepseek_api(messages)
        else:
            raise ValueError(f"Unknown provider: {self.provider}")

    def _call_claude_sdk(self, messages: list[dict]) -> str:
        """
        Call Claude via the Agent SDK.
        In the Claude Code environment, use the built-in Agent tool.
        Outside it, use the anthropic SDK.
        """
        # In Claude Code environment, use our own text generation.
        # The system message + user message are combined into the prompt.
        system_content = ""
        user_messages = []

        for m in messages:
            if m["role"] == "system":
                system_content = m["content"]
            else:
                user_messages.append(m)

        # For Claude Code, we construct a self-contained prompt
        full_prompt = ""
        if system_content:
            full_prompt = system_content + "\n\n---\n\n"

        for m in user_messages:
            full_prompt += m.get("content", "")

        # Use the anthropic package if available
        try:
            import anthropic
            client = anthropic.Anthropic(api_key=self.api_key)
            response = client.messages.create(
                model=self._map_model(),
                max_tokens=self.max_tokens,
                temperature=self.temperature,
                system=system_content if system_content else "You are a Lean 4 expert.",
                messages=[{"role": "user", "content": user_messages[-1]["content"]}],
            )
            # Extract text from response
            for block in response.content:
                if block.type == "text":
                    return block.text
            return str(response.content[0].text) if response.content else ""
        except ImportError:
            raise RuntimeError(
                "anthropic SDK not installed. Install with: pip install anthropic"
            )

    def _call_deepseek_api(self, messages: list[dict]) -> str:
        """Call DeepSeek API (OpenAI-compatible)."""
        import requests

        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {self.api_key}",
        }
        payload = build_deepseek_payload(
            self.model, messages, self.max_tokens, self.temperature
        )
        resp = requests.post(
            "https://api.deepseek.com/v1/chat/completions",
            headers=headers,
            json=payload,
            timeout=600,
        )
        if resp.status_code != 200:
            raise RuntimeError(f"DeepSeek API error {resp.status_code}: {resp.text[:500]}")
        data = resp.json()
        msg = data["choices"][0]["message"]
        # deepseek-reasoner returns reasoning_content + content
        content = msg.get("content", "")
        if not content and "reasoning_content" in msg:
            content = msg["reasoning_content"]
        return content

    def _call_openai_api(self, messages: list[dict]) -> str:
        """Call OpenAI-compatible API."""
        import requests

        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {self.api_key}",
        }
        payload = {
            "model": self.model,
            "messages": messages,
            "max_tokens": self.max_tokens,
            "temperature": self.temperature,
        }
        resp = requests.post(
            "https://api.openai.com/v1/chat/completions",
            headers=headers,
            json=payload,
            timeout=300,
        )
        resp.raise_for_status()
        data = resp.json()
        return data["choices"][0]["message"]["content"]

    def _map_model(self) -> str:
        """Map short model names to full Anthropic model IDs."""
        mapping = {
            "sonnet": "claude-sonnet-5-20250901",
            "opus": "claude-opus-5-20250901",
            "haiku": "claude-haiku-4-5-20251001",
            "claude-sonnet-5": "claude-sonnet-5-20250901",
            "claude-opus-5": "claude-opus-5-20250901",
            "claude-haiku-4-5": "claude-haiku-4-5-20251001",
        }
        return mapping.get(self.model, self.model)

    def _test_connection(self) -> bool:
        """Quick test that API key and endpoint work."""
        try:
            self.generate([{"role": "user", "content": "Say 'ok' and nothing else."}])
            return True
        except Exception as e:
            print(f"Connection test failed: {e}")
            return False

    def _clean_output(self, text: str) -> str:
        """Remove markdown code fences and extract Lean code from mixed output."""
        text = text.strip()

        # If there's a markdown code block, extract the lean code from it
        lean_block_pattern = r'```(?:lean)?\s*\n(.*?)```'
        matches = re.findall(lean_block_pattern, text, re.DOTALL)
        if matches:
            # Use the largest code block (usually the main one)
            return max(matches, key=len).strip()

        # If the text starts with natural language, try to find where code begins
        # Look for "import OnlineScheduling" as the code start marker
        import_match = re.search(r'(import\s+OnlineScheduling.*)', text, re.DOTALL)
        if import_match:
            return import_match.group(1).strip()

        # Remove ``` markers even if incomplete
        text = text.strip()
        if text.startswith("```"):
            lines = text.split("\n")
            if lines[0].startswith("```"):
                lines = lines[1:]
            if lines and lines[-1].strip() == "```":
                lines = lines[:-1]
            text = "\n".join(lines)

        return text.strip()


class MockLLMClient(LLMClient):
    """Mock client for testing without API calls.
    Returns pre-canned responses or echoes the prompt."""

    def __init__(self, response: Optional[str] = None):
        super().__init__()
        self._response = response
        self.call_count = 0
        self.last_messages = None

    def generate(self, messages: list[dict]) -> str:
        self.call_count += 1
        self.last_messages = messages
        if self._response:
            return self._response
        # Echo back the user message for debugging
        last = messages[-1]["content"] if messages else ""
        return f"MOCK RESPONSE to: {last[:200]}..."


if __name__ == "__main__":
    # Quick test
    client = MockLLMClient()
    msgs = [{"role": "user", "content": "Hello"}]
    print(client.generate(msgs))
