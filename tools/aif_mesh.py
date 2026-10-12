#!/usr/bin/env python3
"""Emit the complete shared-node AIF mesh; Lean checks coverage and time joins."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

from aif_metric_pilot import CANDIDATE_SHA256, matrix, vector
from aif_slab_coverage import SELECTIONS


def validate(data: dict) -> None:
    """Reject missing data and nonpositive widths before producing any source."""
    if type(data["denominator"]) is not int or data["denominator"] <= 0:
        raise ValueError("denominator must be a positive integer")
    for key, count in (("time_nodes", 371), ("eta_edges", 9)):
        values = list(map(F, data[key]))
        if len(values) != count or any(a >= b for a, b in zip(values, values[1:])):
            raise ValueError(f"{key} must have {count} strictly increasing entries")
    if len(data["tubes"]) != 8:
        raise ValueError("expected eight parameter bins")
    for raw in data["tubes"]:
        if len(raw) != 6 or any(len(field) != 371 for field in raw):
            raise ValueError("each bin requires six complete 371-node arrays")
        for a, field in enumerate(raw):
            for node in field:
                if len(node) != 4:
                    raise ValueError("each node requires four coordinates or rows")
                if a >= 4 and any(len(row) != 4 for row in node):
                    raise ValueError("each metric requires four columns")
                entries = node if a < 4 else [x for row in node for x in row]
                if any(type(x) is not int for x in entries):
                    raise ValueError("candidate nodal entries must be integers")


def header(name: str, imports: list[str]) -> str:
    """Identify exact candidate bytes without treating the hash as a proof."""
    return "\n".join(f"import {module}" for module in imports) + f"""

/-! Candidate SHA-256: {CANDIDATE_SHA256}.
Geometry and joins only; no unverified drift certificate is assumed. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Gimle.Forseti.Examples.{name}
open AIFMesh AIFSlabModel
open Gimle.Forseti.BernsteinMatrix

"""


def bin_source(data: dict, b: int) -> str:
    """Encode every nodal value once, preserving physical slope arrays."""
    name = f"AIFMeshBin{b}"
    source = header(name, ["Gimle.Forseti.Examples.AIFMesh"])
    raw, denominator = data["tubes"][b], data["denominator"]
    nodes = []
    for k in range(371):
        fields = []
        for a, field in enumerate(("lo", "hi", "loSlope", "hiSlope", "value", "slope")):
            values = raw[a][k]
            rendered = (
                vector([F(x, denominator) for x in values])
                if a < 4
                else matrix([[F(x, denominator) for x in row] for row in values])
            )
            fields.append(f"  {field} := {rendered}")
        nodes.append("{\n" + "\n".join(fields) + "\n}")
    source += (
        "noncomputable def data : Array Knot := #[\n" + ",\n".join(nodes) + "\n]\n"
    )
    source += "\ntheorem data_size : data.size = 371 := rfl\n"
    source += "noncomputable def nodes (i : Fin 371) : Knot := data[i.val]'(by rw [data_size]; exact i.isLt)\n"
    return source + f"end Gimle.Forseti.Examples.{name}\n"


def geometry_source(data: dict) -> str:
    """Check every width and the exact physical coverage endpoints in Lean."""
    source = header("AIFMeshGeometry", ["Gimle.Forseti.Examples.AIFMesh"])
    source += (
        "def times : Fin 371 → ℚ := " + vector(list(map(F, data["time_nodes"]))) + "\n"
    )
    source += (
        "def edges : Fin 9 → ℚ := " + vector(list(map(F, data["eta_edges"]))) + "\n"
    )
    return source + """
def mesh (nodes : Fin 8 → Fin 371 → Knot) : Mesh 370 8 := ⟨times, edges, nodes⟩

theorem time_positive : ∀ i : Fin 370, times i.castSucc < times i.succ := by
  decide +kernel

theorem eta_positive : ∀ b : Fin 8, edges b.castSucc < edges b.succ := by
  decide +kernel

theorem step_positive (nodes : Fin 8 → Fin 371 → Knot) (b : Fin 8) (i : Fin 370) :
    0 < ((mesh nodes).slab b i).step := sub_pos.mpr (time_positive i)

theorem covers (nodes : Fin 8 → Fin 371 → Knot) (t p : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 30) (hp : p ∈ Set.Icc (8 : ℝ) 12) :
    ∃ b : Fin 8, ∃ i : Fin 370,
      t ∈ Set.Icc (((mesh nodes).slab b i).tStart : ℝ)
        ((((mesh nodes).slab b i).tStart : ℝ) + ((mesh nodes).slab b i).step) ∧
      p ∈ Set.Icc (((mesh nodes).slab b i).etaLo : ℝ) (((mesh nodes).slab b i).etaHi : ℝ) := by
  apply Mesh.covers
  · simpa [mesh, times, Matrix.vecHead, Matrix.vecTail] using ht
  · simpa [mesh, edges, Matrix.vecHead, Matrix.vecTail] using hp

#print axioms time_positive
#print axioms eta_positive
#print axioms covers
end Gimle.Forseti.Examples.AIFMeshGeometry
"""


def root_source() -> str:
    """Instantiate every time join for all eight bins using shared candidate nodes."""
    imports = ["Gimle.Forseti.Examples.AIFMeshGeometry"] + [
        f"Gimle.Forseti.Examples.AIFMeshBin{b}" for b in range(8)
    ]
    source = header("AIFCandidateMesh", imports)
    source += (
        "noncomputable def nodes : Fin 8 → Fin 371 → Knot := !["
        + ", ".join(f"AIFMeshBin{b}.nodes" for b in range(8))
        + "]\n"
    )
    return source + """
noncomputable def mesh : Mesh 370 8 := AIFMeshGeometry.mesh nodes

theorem covers (t p : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 30)
    (hp : p ∈ Set.Icc (8 : ℝ) 12) :
    ∃ b : Fin 8, ∃ i : Fin 370,
      t ∈ Set.Icc ((mesh.slab b i).tStart : ℝ)
        (((mesh.slab b i).tStart : ℝ) + (mesh.slab b i).step) ∧
      p ∈ Set.Icc ((mesh.slab b i).etaLo : ℝ) ((mesh.slab b i).etaHi : ℝ) :=
  AIFMeshGeometry.covers nodes t p ht hp

theorem joins (b : Fin 8) (i : Fin 369) :
    Joins (mesh.slab b i.castSucc) (mesh.slab b i.succ) :=
  mesh.joins b i.castSucc i.succ rfl

theorem energy_join (b : Fin 8) (i : Fin 369) (p : ℝ) (x : Fin 4 → ℝ) :
    tubeEnergy (mesh.slab b i.castSucc) (mesh.slab b i.succ).tStart p x =
      tubeEnergy (mesh.slab b i.succ) (mesh.slab b i.succ).tStart p x :=
  (joins b i).tubeEnergy_eq
    (ne_of_gt (AIFMeshGeometry.step_positive nodes b i.castSucc))
    (ne_of_gt (AIFMeshGeometry.step_positive nodes b i.succ)) p x

theorem center_rate_join (b : Fin 8) (i : Fin 369) (u : ℝ) :
    centerRate (mesh.slab b i.castSucc) 1 u = centerRate (mesh.slab b i.succ) 0 u :=
  (joins b i).centerRate_eq
    (ne_of_gt (AIFMeshGeometry.step_positive nodes b i.castSucc))
    (ne_of_gt (AIFMeshGeometry.step_positive nodes b i.succ)) u

theorem metric_rate_join (b : Fin 8) (i : Fin 369) :
    metricRate (mesh.slab b i.castSucc) 1 = metricRate (mesh.slab b i.succ) 0 :=
  (joins b i).metricRate_eq
    (ne_of_gt (AIFMeshGeometry.step_positive nodes b i.castSucc))
    (ne_of_gt (AIFMeshGeometry.step_positive nodes b i.succ))

#print axioms covers
#print axioms joins
#print axioms energy_join
#print axioms center_rate_join
#print axioms metric_rate_join
end Gimle.Forseti.Examples.AIFCandidateMesh
"""


def binding_source(b: int, i: int) -> str:
    """Bind the new representation to each already checked drift slab exactly."""
    name = f"AIFMeshBindingBin{b}Slab{i}"
    old = f"AIFCoverageBin{b}Slab{i}"
    source = header(
        name,
        [
            "Gimle.Forseti.Examples.AIFCandidateMesh",
            f"Gimle.Forseti.Examples.AIFContainmentBin{b}Slab{i}",
        ],
    )
    return source + f"""
deriving instance DecidableEq for Slab

theorem slab_binding : AIFCandidateMesh.mesh.slab {b} {i} = {old}.slab := by
  decide +kernel

theorem drift_in_mesh (t p : ℝ) (e : Fin 4 → ℝ)
    (ht : t ∈ Set.Icc ((AIFCandidateMesh.mesh.slab {b} {i}).tStart : ℝ)
      (((AIFCandidateMesh.mesh.slab {b} {i}).tStart : ℝ) + (AIFCandidateMesh.mesh.slab {b} {i}).step))
    (hp : p ∈ Set.Icc ((AIFCandidateMesh.mesh.slab {b} {i}).etaLo : ℝ)
      ((AIFCandidateMesh.mesh.slab {b} {i}).etaHi : ℝ))
    (he : matrixForm (metric (AIFCandidateMesh.mesh.slab {b} {i})
      (timeCoordinate (AIFCandidateMesh.mesh.slab {b} {i}) t)) e ≤ 1/40000) :
    energyRate (AIFCandidateMesh.mesh.slab {b} {i})
      (timeCoordinate (AIFCandidateMesh.mesh.slab {b} {i}) t)
      (etaCoordinate (AIFCandidateMesh.mesh.slab {b} {i}) p) e ≤
        (1/100) * (1/40000 - matrixForm (metric (AIFCandidateMesh.mesh.slab {b} {i})
          (timeCoordinate (AIFCandidateMesh.mesh.slab {b} {i}) t)) e) - 1/16000000 := by
  rw [slab_binding] at *
  exact AIFContainmentBin{b}Slab{i}.drift_bound_in_tube t p e ht hp he

#print axioms slab_binding
#print axioms drift_in_mesh
end Gimle.Forseti.Examples.{name}
"""


def generate(candidate: Path) -> dict[str, str]:
    """Decode the immutable full candidate and generate all geometric modules."""
    payload = candidate.read_bytes()
    if hashlib.sha256(payload).hexdigest() != CANDIDATE_SHA256:
        raise ValueError("candidate SHA-256 mismatch")
    data = json.loads(gzip.decompress(payload))
    validate(data)
    outputs = {"AIFMeshGeometry.lean": geometry_source(data)}
    outputs.update({f"AIFMeshBin{b}.lean": bin_source(data, b) for b in range(8)})
    outputs["AIFCandidateMesh.lean"] = root_source()
    outputs.update(
        {
            f"AIFMeshBindingBin{b}Slab{i}.lean": binding_source(b, i)
            for b, i in SELECTIONS
        }
    )
    return outputs


def main() -> None:
    """Write generated experiments separately, or check without modifying files."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = generate(args.candidate)
    if not args.check:
        args.output_directory.mkdir(parents=True, exist_ok=True)
    for name, source in outputs.items():
        path = args.output_directory / name
        if args.check:
            if not path.is_file() or path.read_bytes() != source.encode():
                raise SystemExit(f"generated {name} differs")
        else:
            path.write_bytes(source.encode())


if __name__ == "__main__":
    main()
