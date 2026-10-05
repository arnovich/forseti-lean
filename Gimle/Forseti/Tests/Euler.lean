import Gimle.Asgard.Examples.EulerBand

/-! The asgard-lean Euler stream from three modes is part of this release's
build, so a notebook that restates its uniqueness, its kernel-computed
coefficients, its invariants, its certified radius, truncation and band, and
the viscous stream's Gevrey-1 growth finds them compiled, and so is the
classical-solution theorem (`EulerSolution`, task 067, v1.15.0): the field is
an `IsClassicalSolution` on `|t| < 1/648`. This module retains the analytical regression checks from asgard-lean
(tasks 065, 066 and 067). `Tests.EulerContract` additionally checks the
Forseti contract over Asgard's actual Fourier feedback circuit. The one-axis `TruncationBound` with its rational `tailBound` is what
a stream decider lane for trigonometric streams would apply. -/

namespace Gimle.Forseti.Tests.Euler

open Gimle.Asgard.Streams.Torus Gimle.Asgard.Streams.TrigStream Gimle.Asgard.Streams.NS
open Gimle.Asgard.Examples.EulerThreeMode Gimle.Asgard.Examples.EulerBand

example : stream .ogf 0 start 1 (1, 0) = -3 / 40 := euler_t_x

example (n : ℕ) : l1 (stream .ogf 0 start n) ≤ 9 * 648 ^ n := euler_l1 n

example : TruncationBound (stream .ogf 0 start) (1 / 6480) 3 (1 / 100) := truncation

example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    IsClassicalSolution (stream .ogf 0 start) t x := classical ht x

example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    seriesDt (stream .ogf 0 start) t x +
      (-seriesD₂ (psi (stream .ogf 0 start)) t x * seriesD₁ (stream .ogf 0 start) t x +
        seriesD₁ (psi (stream .ogf 0 start)) t x * seriesD₂ (stream .ogf 0 start) t x) = 0 :=
  vorticity_equation ht x

example (x : ℝ × ℝ) :
    analyticField (stream .ogf 0 start) 0 x =
      Real.cos x.1 + Real.cos (x.1 + x.2) + Real.cos (2 * x.1 + x.2) := initial x

example : tailBound 9 648 (1 / 6480) 3 = 1 / 100 := by norm_num [tailBound]

example {t : ℝ} (x : ℝ × ℝ) (ht : |t| ≤ 1 / 6480) :
    |analyticField (stream .ogf 0 start) t x -
      (Real.cos x.1 + Real.cos (x.1 + x.2) + Real.cos (2 * x.1 + x.2))| ≤ 1 / 50 :=
  band x ht

/--
info: 'Gimle.Asgard.Streams.NS.formal_unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.formal_unique
/--
info: 'Gimle.Asgard.Streams.NS.euler_wnorm_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.euler_wnorm_bound
/--
info: 'Gimle.Asgard.Streams.TrigStream.truncationBound_rat'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.TrigStream.truncationBound_rat
/--
info: 'Gimle.Asgard.Streams.NS.gevrey_one'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.gevrey_one
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.euler_t3_x'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.euler_t3_x
/--
info: 'Gimle.Asgard.Examples.EulerBand.euler_l1'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.euler_l1
/--
info: 'Gimle.Asgard.Examples.EulerBand.hasSum_field'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.hasSum_field
/--
info: 'Gimle.Asgard.Examples.EulerBand.truncation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.truncation
/--
info: 'Gimle.Asgard.Examples.EulerBand.band'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.band
/--
info: 'Gimle.Asgard.Examples.EulerBand.viscous_gevrey'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.viscous_gevrey

end Gimle.Forseti.Tests.Euler
