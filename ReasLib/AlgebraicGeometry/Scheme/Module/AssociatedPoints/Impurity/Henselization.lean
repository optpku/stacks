module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Stalk.Henselization
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.Over
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.Limit
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Henselization

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Impurity

/-- An impurity over the spectrum of a chosen henselization of the stalk at `s`
descends to an impurity whose pointed base change is an elementary étale neighbourhood. -/
theorem exists_elementary_of_henselization {X S : Scheme.{u}} (F : X.Modules)
    (f : X ⟶ S) [Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (Rh : Type u) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (h_impurity : Nonempty
      (Over F f s (Scheme.Henselization.map S s Rh) (IsLocalRing.closedPoint Rh))) :
    ∃ I : Impurity F f s, I.IsElementary := sorry

/-- Existence of an impurity over a chosen henselization, over an elementary étale
neighbourhood, and over a morphism finite-type quasi-finite at its special point are
equivalent. -/
theorem existence_tfae {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
    [Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (Rh : Type u) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh] :
    List.TFAE [
      Nonempty (Over F f s (Henselization.map S s Rh) (IsLocalRing.closedPoint Rh)),
      ∃ I : Impurity F f s, I.IsElementary,
      ∃ I : Impurity F f s, Hom.FiniteType.QuasiFiniteAt I.g I.specialPoint] := sorry

/-- Over a chosen henselization of `S` at `s`, there are no impurities if and only if
every relative associated point of the pulled-back module specializes to a point in the
closed fibre. -/
theorem noHenselianImpurity_iff_specializes_closedFiber {X S : Scheme.{u}}
    (F : X.Modules) (f : X ⟶ S) [LocallyOfFiniteType f]
    [F.IsQuasicoherent] [F.IsFiniteType] (s : S) (Rh : Type u) [CommRing Rh]
    [Algebra (S.presheaf.stalk s) Rh] [IsHenselizationOf (S.presheaf.stalk s) Rh] :
    IsEmpty (Over F f s (Henselization.map S s Rh) (IsLocalRing.closedPoint Rh)) ↔
      ∀ x ∈ relativeAssassin (Limits.pullback.snd f (Henselization.map S s Rh))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst f (Henselization.map S s Rh))).obj F),
        ∃ y, Specializes x y ∧
          Limits.pullback.snd f (Henselization.map S s Rh) y =
            IsLocalRing.closedPoint Rh := sorry

end AlgebraicGeometry.Scheme.Modules.Impurity
