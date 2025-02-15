import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Set Filter

open Topology Filter

noncomputable section

-- .. index:: integration
--
-- .. _elementary_integration:
--
-- Elementary Integration
-- ----------------------
--
-- We first focus on integration of functions on finite intervals in ``ℝ``. We can integrate
-- elementary functions.
open MeasureTheory intervalIntegral

open Interval
-- this introduces the notation `[[a, b]]` for the segment from `min a b` to `max a b`

example (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) : (∫ x in a..b, 1 / x) = Real.log (b / a) :=
  integral_one_div h

-- The fundamental theorem of calculus relates integration and differentiation.
-- Below we give simplified statements of the two parts of this theorem. The first part
-- says that integration provides an inverse to differentiation and the second one
-- specifies how to compute integrals of derivatives.
-- (These two parts are very closely related, but their optimal versions,
-- which are not shown here, are not equivalent.)
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) : deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
        hf.continuousAt).hasDerivAt.deriv

example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ} (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) : (∫ y in a..b, f' y) = f b - f a :=
  integral_eq_sub_of_hasDerivAt h h'

-- Convolution is also defined in Mathlib and its basic properties are proved.
open Convolution

example (f : ℝ → ℝ) (g : ℝ → ℝ) : f ⋆ g = fun x ↦ ∫ t, f t * g (x - t) :=
  rfl


-- https://www.youtube.com/watch?v=Ff4LRlflib0
-- using complex analysis (cauchy integral theorem)
example (f : ℝ → ℝ) (a b c : ℝ) (h1 : IntegrableOn f (Set.Ioo a b) volume) (h2 : IntegrableOn f (Set.Ioo b c) volume) (h3 : IntegrableOn f (Set.Ioo a c) volume) : a < b → b < c → ∫ x in a..b, f x  = ∫ x in (0 : ℝ)..b, f x  - ∫ x in (0 : ℝ)..a, f x := by
{
  intros hab hbc
  have : deriv (fun x => ∫ t in (0)..x, f t) = f := by library_search
}
example (f : ℝ → ℝ) (hf : IntegrableOn f Set.univ volume) : ∫ x in Set.univ, f x = ∫ x in (Set.Iio 0), f x + ∫ x in (Set.Ici 0), f x := by
{
  library_search
}

-- #check Integrable
-- #check CircleIntegrable
-- #check IntervalIntegrable
