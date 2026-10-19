import Gimle.Forseti.Examples.AIFMesh

/-! Mesh boundaries and hostile join regressions. -/
namespace Gimle.Forseti.Tests.AIFMesh
open Gimle.Forseti.Examples.AIFSlabModel Gimle.Forseti.Examples.AIFMesh
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix

def node (k : Fin 3) : Knot where
  lo := fun _ => k
  hi := fun _ => k + 1
  loSlope := fun _ => 2
  hiSlope := fun _ => 3
  value := fun i j => if i = j then k + 1 else 0
  slope := fun i j => if i = j then 5 else 0

def mesh : Mesh 2 1 where
  times := ![0, 1/200, 1/40]
  edges := ![8, 17/2]
  nodes := fun _ => node

example : Joins (mesh.slab 0 0) (mesh.slab 0 1) :=
  mesh.joins 0 0 1 rfl

example (p : ℝ) (x : Fin 4 → ℝ) :
    tubeEnergy (mesh.slab 0 0) (1/200) p x =
      tubeEnergy (mesh.slab 0 1) (1/200) p x := by
  have ht : ((mesh.slab 0 1).tStart : ℝ) = 1/200 := by
    norm_num [Mesh.slab, mesh]
  simpa only [ht] using (mesh.joins 0 0 1 rfl).tubeEnergy_eq
    (by decide +kernel) (by decide +kernel) p x

example (t p : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/40))
    (hp : p ∈ Set.Icc (8 : ℝ) (17/2)) :
    ∃ b : Fin 1, ∃ i : Fin 2,
      t ∈ Set.Icc ((mesh.slab b i).tStart : ℝ)
        (((mesh.slab b i).tStart : ℝ) + (mesh.slab b i).step) ∧
      p ∈ Set.Icc ((mesh.slab b i).etaLo : ℝ) ((mesh.slab b i).etaHi : ℝ) :=
  mesh.covers t p (by simpa [mesh, Matrix.vecHead, Matrix.vecTail] using ht)
    (by simpa [mesh, Matrix.vecHead, Matrix.vecTail] using hp)

-- Altering either endpoint data or time adjacency must break the join.
example : ¬ Joins (mesh.slab 0 0)
    { mesh.slab 0 1 with startMetric := 0 } := by
  intro h
  have he := congrFun (congrFun h.metric 0) 0
  norm_num [Mesh.slab, mesh, node] at he

example : ¬ Joins (mesh.slab 0 0)
    { mesh.slab 0 1 with loStart := fun _ => 99 } := by
  intro h
  have he := congrFun h.lo 0
  norm_num [Mesh.slab, mesh, node] at he

example : ¬ Joins (mesh.slab 0 0)
    { mesh.slab 0 1 with tStart := 1/100 } := by
  intro h
  have he := h.time
  norm_num [Mesh.slab, mesh, Matrix.vecHead, Matrix.vecTail] at he

example : ¬ Joins (mesh.slab 0 0)
    { mesh.slab 0 1 with startMetricSlope := 0 } := by
  intro h
  have he := congrFun (congrFun h.metricSlope 0) 0
  norm_num [Mesh.slab, mesh, node] at he

-- Both ends, including the last node, belong to a mesh interval.
example : ∃ i : Fin 2, (1/40 : ℝ) ∈
    Set.Icc (mesh.times i.castSucc : ℝ) (mesh.times i.succ : ℝ) :=
  interval_covered 1 (fun i => (mesh.times i : ℝ)) _ (by norm_num [mesh, Fin.last, Matrix.cons_val_two])

end Gimle.Forseti.Tests.AIFMesh
