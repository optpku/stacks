module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan

/-- Restriction identifies flat, separated, locally finite-type and locally quasi-finite
schemes over an admissible pushout with compatible such schemes over its two components. -/
@[instance]
theorem flatBaseChangeIsEquivalence {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    Functor.IsEquivalence
      (baseChange
        ((@Flat ⊓ @IsSeparated ⊓ @LocallyOfFiniteType ⊓ @LocallyQuasiFinite) :
          MorphismProperty Scheme.{u}) i.left j.left) := sorry

/-- Restriction identifies étale, separated, locally finite-type and locally quasi-finite
schemes over an admissible pushout with compatible such schemes over its two components. -/
@[instance]
theorem etaleBaseChangeIsEquivalence {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    Functor.IsEquivalence
      (baseChange
        ((@Etale ⊓ @IsSeparated ⊓ @LocallyOfFiniteType ⊓ @LocallyQuasiFinite) :
          MorphismProperty Scheme.{u}) i.left j.left) := sorry

/-- Restriction identifies finite étale schemes over an admissible pushout with
compatible finite étale schemes over its two components. -/
theorem finiteEtaleBaseChangeIsEquivalence {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j] :
    Functor.IsEquivalence
      (Scheme.Pushout.baseChange Scheme.finiteEtaleMorphism i.left j.left) := sorry

end AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan
