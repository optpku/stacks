module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.Homotopy.Contractible
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex

/-!
# Contractible Naive Cotangent Complexes

This leaf isolates the two-term contraction mechanism from any particular
reason that a presentation's cotangent differential is invertible.  It also
records a reusable criterion for that differential to be bijective.
-/

@[expose] public section

open CategoryTheory

universe u v w

noncomputable section

namespace Algebra.Extension.NaiveCotangent.Contractible

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The cotangent differential of a presentation is bijective when both its first cotangent
homology and the Kahler differentials of the target are subsingleton. -/
@[stacks 07BR "two-term cotangent contraction"]
theorem cotangentComplexBijective
    (P : Extension.{w} R S)
    [Subsingleton P.H1Cotangent] [Subsingleton Ω[S⁄R]] :
    Function.Bijective P.cotangentComplex := sorry

/-- The degree-lowering map associated to a chosen inverse of a presentation's cotangent
differential. -/
@[stacks 07BR "two-term cotangent contraction"]
noncomputable def contraction
    (P : Extension.{w} R S)
    (σ : P.CotangentSpace →ₗ[S] P.Cotangent)
    (i j : ℕ) (_ : (ComplexShape.down ℕ).Rel j i) :
    (complex P).X i ⟶ (complex P).X j :=
  match i, j with
  | 0, 1 => ModuleCat.ofHom (liftCotangentSpaceMap P σ)
  | _, _ => 0

/-- A two-term naive cotangent complex is null-homotopic whenever the cotangent differential
has the displayed two-sided inverse. -/
@[stacks 07BR "two-term cotangent contraction"]
theorem id_eq_nullHomotopicMap
    (P : Extension.{w} R S)
    (σ : P.CotangentSpace →ₗ[S] P.Cotangent)
    (hleft : P.cotangentComplex.comp σ = LinearMap.id)
    (hright : σ.comp P.cotangentComplex = LinearMap.id) :
    𝟙 (complex P) = Homotopy.nullHomotopicMap' (contraction P σ) := sorry

/-- The explicit null-homotopy determined by a two-sided inverse of the cotangent
differential. -/
@[stacks 07BR "two-term cotangent contraction"]
noncomputable def homotopy
    (P : Extension.{w} R S)
    (σ : P.CotangentSpace →ₗ[S] P.Cotangent)
    (hleft : P.cotangentComplex.comp σ = LinearMap.id)
    (hright : σ.comp P.cotangentComplex = LinearMap.id) :
    Homotopy (𝟙 (complex P)) 0 :=
  (Homotopy.ofEq (id_eq_nullHomotopicMap P σ hleft hright)).trans
    (Homotopy.nullHomotopy' (contraction P σ))

/-- A naive cotangent complex is homotopy equivalent to zero when its cotangent differential
has a specified two-sided inverse. -/
@[stacks 07BR "two-term cotangent contraction"]
noncomputable def homotopyEquivZero
    (P : Extension.{w} R S)
    (σ : P.CotangentSpace →ₗ[S] P.Cotangent)
    (hleft : P.cotangentComplex.comp σ = LinearMap.id)
    (hright : σ.comp P.cotangentComplex = LinearMap.id) :
    HomotopyEquiv (complex P)
      (HomologicalComplex.zero : ChainComplex (ModuleCat.{max v w} S) ℕ) :=
  Homotopy.equivZero (homotopy P σ hleft hright)

end Algebra.Extension.NaiveCotangent.Contractible
