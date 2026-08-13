# Lean Theorem Proving SFT Training

One-stop workflow for fine-tuning a 7B model on Lean 4 online scheduling proofs.

## When to use

User wants to train/fine-tune a model on Lean theorem proving data, generate training data from Lean source files, run QLoRA training, or use a trained model for inference.

## Environment

| Component | Version/Path |
|-----------|-------------|
| Python | 3.11 |
| PyTorch | 2.5.1+cu121 |
| CUDA | 12.8 driver, 12.1 toolkit |
| GPU | RTX 4090 D, 24.5GB |
| Base model | `/root/autodl-tmp/models/deepseek-math-7b-base` |
| LLaMA-Factory | `/root/autodl-tmp/LLaMA-Factory` |
| Lean project | `/root/autodl-tmp/OnlineScheduling` |
| Gitee sync | `/root/autodl-tmp/ai4math` (branch `lean-online-scheduling`) |

## Quick Start: Launch Training

```bash
cd /root/autodl-tmp/LLaMA-Factory

# 1. Prepare Alpaca-format training data
python3 -c "
import json; data = json.load(open('data/train_v9_alpaca.json'))
print(f'{len(data)} samples')
"

# 2. Register dataset
python3 -c "
import json; d = json.load(open('data/dataset_info.json'))
d['my_dataset'] = {'file_name': 'train_v9_alpaca.json'}
json.dump(d, open('data/dataset_info.json','w'), indent=2)
"

# 3. Create config (copy template below)
mkdir -p llamafactory_runs/my_run

# 4. Launch training
CUDA_VISIBLE_DEVICES=0 nohup llamafactory-cli train llamafactory_runs/my_run/sft.yaml \
  > llamafactory_runs/my_run/train.log 2>&1 &

# 5. Check progress
tr '\r' '\n' < llamafactory_runs/my_run/train.log | grep -oE "[0-9]+/[0-9]+" | tail -1
grep "train_loss" llamafactory_runs/my_run/train.log | tail -3
```

## Training Config Template

```yaml
### model
model_name_or_path: /root/autodl-tmp/models/deepseek-math-7b-base
trust_remote_code: true
### method
stage: sft
do_train: true
finetuning_type: lora
lora_rank: 64
lora_alpha: 128
lora_target: all
quantization_bit: 4
quantization_method: bnb
double_quantization: true
### dataset
dataset: my_dataset_name
template: deepseek
cutoff_len: 2048
### output
output_dir: saves/deepseek-math-7b/qlora/my_run
logging_steps: 5
save_steps: 100
plot_loss: true
overwrite_output_dir: true
report_to: none
### train
per_device_train_batch_size: 1
gradient_accumulation_steps: 4
learning_rate: 1.0e-4
num_train_epochs: 5.0
lr_scheduler_type: cosine
warmup_ratio: 0.1
bf16: true
ddp_timeout: 180000000
```

## Generating Training Data

### M5 Gap-Filling from Basic.lean

```python
# cd /root/autodl-tmp/OnlineScheduling
# Run: python3 experiments/gen_m5.py (create if not exists)
# Key parameters:
# - SAFE patterns: exact, simpa, linarith, nlinarith, rw, apply, ring, field_simp, simp, dsimp, norm_num, positivity
# - BLOCKED: induction, case, · (bullet), . (dot)
# - Output format: JSONL with lean_prompt (code with sorry) + lean_answer (the removed tactic)
```

### Counterexample Generation (Python) 

```python
# For P2/P3/P4, enumerate all job assignments (small instances only)
# P2: [1,1,2] on 2 machines = 2^3 = 8 assignments
# P3: [1x6, 3] = 3^7 = 2187 assignments
# Output: NL prompts + verified numerical answers
```

## Using Trained Models

```python
# /root/autodl-tmp/inference.py
import torch; from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import PeftModel

model = AutoModelForCausalLM.from_pretrained(
    "/root/autodl-tmp/models/deepseek-math-7b-base",
    torch_dtype=torch.bfloat16, device_map="auto", trust_remote_code=True)
model = PeftModel.from_pretrained(model, "/root/backups/r1")
tokenizer = AutoTokenizer.from_pretrained("/root/autodl-tmp/models/deepseek-math-7b-base", trust_remote_code=True)

prompt = "import OnlineScheduling.Basic\n\nopen OnlineScheduling\n\nlemma ... := by\n  sorry"
inputs = tokenizer(prompt, return_tensors="pt").to(model.device)
with torch.no_grad():
    out = model.generate(**inputs, max_new_tokens=256, temperature=0.3, do_sample=True)
print(tokenizer.decode(out[0], skip_special_tokens=True)[len(prompt):])
```

## Saved Models

| Round | Adapter Path | Loss | Data |
|:--:|------|:--:|------|
| R1 | `/root/backups/round1` | **0.02** | 88 gap-filling (best) |
| R2 | `/root/backups/round2` | 0.27 | 88, lower lr |
| R3 | `/root/backups/r3` | 0.33 | +typecheck (no answer) |
| R4 | `/root/backups/r4` | 0.33 | +M5_safe_gap |
| R5 | `/root/backups/r5` | 0.32 | +counterexample (NL) |
| R6 | `/root/backups/r6` | 0.28 | +M5_relaxed (Lean) |
| R7 | `/root/backups/r7` | 0.29 | +more NL samples |

## Key Lessons

1. **Only Lean→Lean gap-filling data works.** NL samples dilute the signal.
2. **88 high-quality samples > 228 mixed samples.**
3. **M5 generation**: don't randomly delete lines; use safe patterns with relaxed filtering (only exclude induction/case/·).
4. **lr=1e-4, epochs=5** gave the best results.

## Gitee Sync

```bash
cd /root/autodl-tmp/ai4math
# Pull latest Lean fixes
GIT_ASKPASS=/tmp/gitee_askpass.sh git pull origin lean-online-scheduling
# Copy to project
cp OnlineScheduling/Algorithms/*.lean ../OnlineScheduling/OnlineScheduling/Algorithms/
cp OnlineScheduling/LowerBounds/*.lean ../OnlineScheduling/OnlineScheduling/LowerBounds/
# Build and check
cd /root/autodl-tmp/OnlineScheduling && lake build
```

## Lean Compilation

```bash
cd /root/autodl-tmp/OnlineScheduling
lake build  # all 23 modules compile
lake env lean OnlineScheduling/Basic.lean  # test single file
```
