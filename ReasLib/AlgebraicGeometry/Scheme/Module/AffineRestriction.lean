module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Restriction
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Scalar compatibility for the affine-open identification of module sections with
global sections of the restriction along `fromSpec`. -/
private theorem affineOpenRestrictSectionsIso_smul {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (M : X.Modules) (r : Γ(X, U)) :
    (M.presheaf.mapIso
            (eqToIso
              (hU.fromSpec.image_top_eq_opensRange.trans
                hU.opensRange_fromSpec)).op).hom ≫
        (M.restrictAppIso hU.fromSpec ⊤).inv ≫
          ((moduleSpecΓFunctor (R := Γ(X, U))).obj
            ((Scheme.Modules.restrictFunctor hU.fromSpec).obj M)).smul r =
      ((SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)).obj M).smul r ≫
        (M.presheaf.mapIso
            (eqToIso
              (hU.fromSpec.image_top_eq_opensRange.trans
                hU.opensRange_fromSpec)).op).hom ≫
          (M.restrictAppIso hU.fromSpec ⊤).inv :=
  sorry

/-- Canonical identification of sections of `M` on an affine open `U` with global
sections of the restriction of `M` along `hU.fromSpec`. -/
noncomputable def affineOpenRestrictSectionsIso {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (M : X.Modules) :
    (SheafOfModules.evaluation.{u} X.ringCatSheaf (op U)).obj M ≅
      (moduleSpecΓFunctor (R := Γ(X, U))).obj
        ((Scheme.Modules.restrictFunctor hU.fromSpec).obj M) :=
  ModuleCat.isoMk
    (M.presheaf.mapIso
        (eqToIso
          (hU.fromSpec.image_top_eq_opensRange.trans
            hU.opensRange_fromSpec)).op ≪≫
      (M.restrictAppIso hU.fromSpec ⊤).symm)
    (by exact affineOpenRestrictSectionsIso_smul hU M)

/-- Identification of pullback along `Spec` of restriction of functions on nested
affine opens with restriction along `fromSpec` of the smaller open. -/
noncomputable def nestedAffinePullbackIso {X : Scheme.{u}} {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hLE : U' ≤ U) :
    Scheme.Modules.restrictFunctor hU.fromSpec ⋙
        Scheme.Modules.pullback (Spec.map (X.presheaf.map (homOfLE hLE).op)) ≅
      Scheme.Modules.restrictFunctor hU'.fromSpec :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec)
      (Scheme.Modules.pullback (Spec.map (X.presheaf.map (homOfLE hLE).op))) ≪≫
    Scheme.Modules.pullbackComp (Spec.map (X.presheaf.map (homOfLE hLE).op))
      hU.fromSpec ≪≫
    Scheme.Modules.pullbackCongr
      (IsAffineOpen.map_fromSpec hU hU' (homOfLE hLE).op) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback hU'.fromSpec).symm

end AlgebraicGeometry.Scheme.Modules
