import Gimle.Forseti.BernsteinConversion
import Gimle.Forseti.Examples.AIFMeshComposition
import Gimle.Forseti.Examples.AIFPolynomialBinding
import Gimle.Forseti.Examples.AIFSlabContainment
import Gimle.Forseti.Examples.AIFSlabData
import Gimle.Forseti.RationalLDL

/-! The in-tube drift inequality on one AIF slab, derived from checked rational
certificates: symmetric endpoint data, four containment matrices bounding the error
coordinate `e₂`, and two drift-block Bernstein tables at the error extremes
`±3/200`. With one such bundle per cell, the moving-tube bound of
`AIFMeshComposition` holds with no supplied drift inequality. Solutions and their
derivatives are still hypotheses here. -/
namespace Gimle.Forseti.Examples.AIFSlabDrift
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open AIFSlabModel AIFMesh

/-- A Bernstein table for the drift block at one error value, its square
certificates and its binding to the slab's block at every point. -/
structure BlockCertificate (d : Slab) (ec : ℚ) where
  timeDegree : Nat
  parameterDegree : Nat
  coefficients : Fin (timeDegree + 1) → Fin (parameterDegree + 1) → QMatrix 5
  squares : Fin (timeDegree + 1) → Fin (parameterDegree + 1) → WeightedSquares 5
  valid : ∀ i j, (squares i j).Represents (coefficients i j)
  binding : ∀ s u, block d s u ec = tensorMatrix coefficients s u

/-- The binding is supplied by the exact rational polynomial test, for a table that
is written out rather than computed. -/
def BlockCertificate.ofCheck {td pd : Nat} (d : Slab) (ec : ℚ)
    (c : Fin (td + 1) → Fin (pd + 1) → QMatrix 5)
    (squares : Fin (td + 1) → Fin (pd + 1) → WeightedSquares 5)
    (valid : ∀ i j, (squares i j).Represents (c i j))
    (checked : ∀ i j, RationalPolynomial.equivalent
      (AIFPolynomialBinding.block d ec i j) (AIFPolynomialBinding.tensor c i j) = true) :
    BlockCertificate d ec where
  timeDegree := td
  parameterDegree := pd
  coefficients := c
  squares := squares
  valid := valid
  binding := AIFPolynomialBinding.binding d ec c checked

/-- The table is computed from the slab's block polynomial and each square
certificate is recomputed from its matrix, so no table or square data is written
out; the binding needs only the degree check. -/
def BlockCertificate.ofComputed {td pd : Nat} (d : Slab) (ec : ℚ)
    (degree : ∀ i j, BernsteinConversion.withinDegree td pd
      (AIFPolynomialBinding.block d ec i j) = true)
    (valid : ∀ a b, (RationalLDL.propose
      (BernsteinConversion.table td pd (AIFPolynomialBinding.block d ec) a b)).Represents
        (BernsteinConversion.table td pd (AIFPolynomialBinding.block d ec) a b)) :
    BlockCertificate d ec where
  timeDegree := td
  parameterDegree := pd
  coefficients := BernsteinConversion.table td pd (AIFPolynomialBinding.block d ec)
  squares := fun a b => RationalLDL.propose
    (BernsteinConversion.table td pd (AIFPolynomialBinding.block d ec) a b)
  valid := valid
  binding := by
    intro s u
    rw [← BernsteinConversion.table_binding td pd _ degree s u]
    ext i j
    exact (AIFPolynomialBinding.eval_block d ec s u i j).symm

theorem BlockCertificate.nonnegative {d : Slab} {ec : ℚ} (c : BlockCertificate d ec)
    {s u : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin 5 → ℝ) : 0 ≤ matrixForm (block d s u ec) x :=
  target_nonnegative c.squares c.valid (c.binding s u) hs hu x

/-- Everything one slab needs for its drift inequality. -/
structure CellCertificates (d : Slab) where
  symmetric : AIFSlabData.SymmetricData d
  error : Fin 4 → Fin 1 → WeightedSquares 4
  errorValid : ∀ i j, (error i j).Represents (AIFSlabContainment.errorCoefficients d i j)
  negative : BlockCertificate d (-3/200)
  positive : BlockCertificate d (3/200)

/-- The drift premise of `AIFInvariance.tube_invariant`, from certificates and a
nondegenerate cell. -/
theorem drift_in_tube (d : Slab) (certificates : CellCertificates d)
    (width : 0 < d.step) (eta_ordered : d.etaLo < d.etaHi) :
    ∀ t q e,
      t ∈ Set.Icc (d.tStart : ℝ) ((d.tStart : ℝ) + d.step) →
      q ∈ Set.Icc (d.etaLo : ℝ) (d.etaHi : ℝ) →
      matrixForm (metric d (timeCoordinate d t)) e ≤ 1/40000 →
      energyRate d (timeCoordinate d t) (etaCoordinate d q) e ≤
        (1/100) * (1/40000 - matrixForm (metric d (timeCoordinate d t)) e) - 1/16000000 := by
  intro t q e ht hq he
  have hs := timeCoordinate_mem d width t ht
  have hu := etaCoordinate_mem d eta_ordered q hq
  have negative : ((-3/200 : ℚ) : ℝ) = -1*(3/200) := by push_cast; ring
  have positive : ((3/200 : ℚ) : ℝ) = 1*(3/200) := by push_cast; ring
  have hn := fun x => negative ▸ certificates.negative.nonnegative hs hu x
  have hpos := fun x => positive ▸ certificates.positive.nonnegative hs hu x
  exact drift_bound d _ _ e (AIFSlabData.metric_symmetric d certificates.symmetric _) hn hpos
    (AIFSlabContainment.error_contained_of_certificates d certificates.error
      certificates.errorValid _ hs e he)

/-- `AIFMeshComposition.mesh_invariant` with every cell's drift discharged by its
certificates. The solution and its derivatives remain hypotheses. -/
theorem mesh_invariant_of_certificates {nt nb : Nat} (m : Mesh (nt + 1) nb) (b : Fin nb)
    (widths : ∀ i, 0 < (m.slab b i).step)
    (eta_ordered : m.edges b.castSucc < m.edges b.succ)
    (p : ℝ) (hp : p ∈ Set.Icc (m.edges b.castSucc : ℝ) (m.edges b.succ : ℝ))
    (state : ℝ → Fin 4 → ℝ)
    (derivative : ∀ i : Fin (nt + 1), ∀ t ∈ Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ), ∀ j,
      HasDerivWithinAt (fun z => state z j) (AIFDriftModel.field p (state t) j)
        (Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ)) t)
    (certificates : ∀ i, CellCertificates (m.slab b i))
    (initial : tubeEnergy (m.slab b 0) (m.times 0) p (state (m.times 0)) ≤ 1/40000) :
    ∀ i, ∀ t ∈ Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ),
      tubeEnergy (m.slab b i) t p (state t) ≤ 1/40000 := by
  apply AIFMeshComposition.mesh_invariant m b widths eta_ordered p hp state derivative _ initial
  intro i t q e ht hq he
  have hs : ((m.slab b i).tStart : ℝ) = (m.times i.castSucc : ℝ) := rfl
  have hend : (m.times i.castSucc : ℝ) + (m.slab b i).step = (m.times i.succ : ℝ) := by
    simp [Mesh.slab]
  exact drift_in_tube (m.slab b i) (certificates i) (widths i) eta_ordered t q e
    (by rw [hs, hend]; exact ht) hq he

#print axioms BlockCertificate.nonnegative
#print axioms drift_in_tube
#print axioms mesh_invariant_of_certificates
end Gimle.Forseti.Examples.AIFSlabDrift
