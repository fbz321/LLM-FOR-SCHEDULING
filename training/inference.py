"""Use trained LoRA model for Lean proof generation."""
import torch, json
from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import PeftModel

class LeanProver:
    def __init__(self, base_model: str, adapter_path: str):
        print(f"Loading {adapter_path}...")
        self.model = AutoModelForCausalLM.from_pretrained(
            base_model, torch_dtype=torch.bfloat16, device_map="auto", trust_remote_code=True)
        self.model = PeftModel.from_pretrained(self.model, adapter_path)
        self.tokenizer = AutoTokenizer.from_pretrained(base_model, trust_remote_code=True)

    def generate(self, prompt: str, max_tokens: int = 512, temperature: float = 0.3) -> str:
        inputs = self.tokenizer(prompt, return_tensors="pt").to(self.model.device)
        with torch.no_grad():
            out = self.model.generate(**inputs, max_new_tokens=max_tokens,
                temperature=temperature, do_sample=True, pad_token_id=self.tokenizer.eos_token_id)
        full = self.tokenizer.decode(out[0], skip_special_tokens=True)
        return full[len(prompt):].strip()

# ── Usage ──
if __name__ == "__main__":
    import sys
    rounds = {
        'r1': '/root/backups/round1',
        'r2': '/root/backups/round2',
        'r3': '/root/backups/r3',
        'r4': '/root/backups/r4',
        'r5': '/root/backups/r5',
        'r6': '/root/backups/r6',
        'r7': '/root/backups/r7',
    }
    r = sys.argv[1] if len(sys.argv) > 1 else 'r1'
    adapter = rounds.get(r, rounds['r1'])
    print(f"Using {r}: {adapter} (loss: {round(88,2)})")

    prover = LeanProver(
        base_model="/root/autodl-tmp/models/deepseek-math-7b-base",
        adapter_path=adapter,
    )

    prompt = """import OnlineScheduling.Basic
open OnlineScheduling

lemma maxJobSize_nonneg (σ : JobSequence) (h : ∀ p ∈ σ, 0 ≤ p) : 0 ≤ maxJobSize σ := by
  sorry"""

    result = prover.generate(prompt)
    print("Generated:")
    print(result)
