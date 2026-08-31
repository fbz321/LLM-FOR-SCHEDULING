#!/usr/bin/env python3
"""Generate and audit Rudin's m=5 Table A2 fixed adversarial sequence.

The dissertation publishes enough information to reproduce the mathematical
Type-2/Type-3 recurrences, but not the hidden spreadsheet precision or the
optimization constraints that selected the three initial Type-1 rows.  The
``published`` mode therefore treats Table A2's printed decimal strings as the
authoritative finite certificate.  ``formula_audit`` recomputes the formula-
derived rows and reports their difference from the printed table; it must not
be mistaken for a bit-for-bit reconstruction of the unpublished spreadsheet.
"""

import argparse
import json
import os
from decimal import Decimal, getcontext

getcontext().prec = 80

M = 5
PUBLISHED_RATIO = "1.74833497030641"
V_PRINTED = Decimal(PUBLISHED_RATIO) - 1
SCALE = Decimal(10) ** 13

# (decimal string, multiplicity, layer kind)
TABLE_A2 = (
    ("3.3286757562613", 5, "type1"),
    ("20.9660370171070", 5, "type1"),
    ("72.2411976904251", 5, "type1"),
    ("287.052983795090", 5, "type2-b"),
    ("899.596995949914", 4, "type2-a"),
    ("1044.07939133076", 1, "type2-singleton"),
    ("4148.68681835519", 5, "type2-b"),
    ("12587.4513561792", 4, "type2-a"),
    ("14386.6453480790", 1, "type2-singleton"),
    ("57165.8500412044", 5, "type2-b"),
    ("173242.745546272", 4, "type2-a"),
    ("198417.648258631", 1, "type2-singleton"),
    ("788419.624690050", 5, "type2-b"),
    ("2387543.74097628", 4, "type2-a"),
    ("2734029.23206882", 1, "type2-singleton"),
    ("10863762.9765152", 5, "type2-b"),
    ("32895740.0963689", 4, "type2-a"),
    ("37670827.5783215", 1, "type2-singleton"),
    ("95000503.3523561", 4, "type3-a"),
    ("138933850.066262", 1, "type3-singleton"),
)
FINAL = ("190001006.704712", 1)
TYPE2_STARTS = (3, 6, 9, 12, 15)


def printed_decimal_to_integer(text):
    """Apply the seed's exact Table A2 transcription rule (decimal × 10^13)."""
    whole, separator, fractional = text.partition(".")
    if not separator:
        fractional = ""
    fractional = (fractional + "0" * 13)[:13]
    return int(whole) * 10 ** 13 + int(fractional)


def published_jobs():
    jobs = []
    for text, repeat, _ in TABLE_A2:
        jobs.extend([printed_decimal_to_integer(text)] * repeat)
    final_text, repeat = FINAL
    jobs.extend([printed_decimal_to_integer(final_text)] * repeat)
    return tuple(jobs)


def published_template():
    layers = []
    for text, repeat, kind in TABLE_A2:
        layers.append({
            "kind": kind,
            "emit": [{
                "repeat": repeat,
                "size": str(printed_decimal_to_integer(text)),
                "published_decimal": text,
            }],
        })
    final_text, repeat = FINAL
    return {
        "schema_version": 1,
        "name": "rudin2001_m5 (Table A2 authoritative transcription)",
        "description": (
            "Rudin 2001 Table A2; printed decimals independently scaled by "
            "10^13. Recurrence metadata is explanatory, while the printed "
            "table is authoritative because spreadsheet guard digits and "
            "initial optimization constraints were not published."
        ),
        "m": M,
        "layers": layers,
        "final": [{
            "repeat": repeat,
            "size": str(printed_decimal_to_integer(final_text)),
            "published_decimal": final_text,
        }],
        "order": "fwd",
        "known_value": PUBLISHED_RATIO,
        "metadata": {
            "source": "Rudin 2001 dissertation, Table A2",
            "scale": "10000000000000",
            "rounding": "printed decimal string padded/truncated to 13 places",
            "type2_stages": 5,
            "type3_stages": 1,
            "printed_v": str(V_PRINTED),
            "formula_limit": (
                "Published V and initial rows lack hidden spreadsheet guard "
                "digits; formula mode is an audit, not the authoritative seed."
            ),
            "type2_formulas": {
                "B": "((1+V)*D_C-S_C)/(1-V)",
                "A": "(V*B+2*V*C-S_C)/(1-V)",
                "singleton": "A+2*C",
            },
            "type3_formulas": {
                "A": "(2*V*B-S_B)/(1-V)",
                "R_reverse": "(1-V*R_A)/(2*V*(1-R_A))",
                "divisor": "A+2*B",
                "forcing_job": "(1+V)*divisor-S_A",
            },
        },
    }


def formula_audit():
    """Recompute Type-2 formula rows from printed V and initial Type-1 rows."""
    printed = [Decimal(text) for text, _, _ in TABLE_A2]
    type1 = printed[:3]
    stack = sum(type1)
    previous_a = type1[-1]
    divisor = stack
    rows = []

    for stage, start in enumerate(TYPE2_STARTS, 1):
        b = ((1 + V_PRINTED) * divisor - stack) / (1 - V_PRINTED)
        a = (V_PRINTED * b + 2 * V_PRINTED * previous_a - stack) / (
            1 - V_PRINTED
        )
        singleton = a + 2 * previous_a
        expected = printed[start:start + 3]
        generated = (b, a, singleton)
        rows.append({
            "stage": stage,
            "generated": [str(value) for value in generated],
            "published": [str(value) for value in expected],
            "absolute_error": [
                str(abs(value - target))
                for value, target in zip(generated, expected)
            ],
        })
        stack += b + a
        divisor = a + b + 2 * previous_a
        previous_a = a

    # Auditing the final optimized Type-3 row directly from the printed table
    # is meaningful even though the formula-only Type-2 guard digits drift.
    stack_b = sum(printed[index] for index in (0, 1, 2, 3, 4, 6, 7, 9,
                                               10, 12, 13, 15, 16))
    b = printed[16]
    a = printed[18]
    divisor = a + 2 * b
    stack_a = stack_b + a
    forcing = (1 + V_PRINTED) * divisor - stack_a
    rows.append({
        "stage": "final-type3-from-published-prefix",
        "generated": [str(a), str(forcing), str(2 * a)],
        "published": [printed[18].to_eng_string(),
                      printed[19].to_eng_string(), FINAL[0]],
        "absolute_error": [
            "0",
            str(abs(forcing - printed[19])),
            str(abs(2 * a - Decimal(FINAL[0]))),
        ],
    })
    return {
        "printed_v": str(V_PRINTED),
        "authoritative": False,
        "reason": (
            "Table A2 was optimized with unpublished spreadsheet precision; "
            "the audit uses only displayed inputs."
        ),
        "rows": rows,
    }


def atomic_json(path, payload):
    directory = os.path.dirname(os.path.abspath(path))
    os.makedirs(directory, exist_ok=True)
    temporary = path + ".tmp"
    with open(temporary, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
    os.replace(temporary, path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("published", "audit"),
                        default="published")
    parser.add_argument("--output")
    args = parser.parse_args()

    payload = published_template() if args.mode == "published" else formula_audit()
    if args.output:
        atomic_json(args.output, payload)
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
