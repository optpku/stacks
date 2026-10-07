module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# Nonzero sections of flat locally quasi-finite morphisms

This module records how a nonzero global function can be retained after restricting to
compatible opens and embedded into a pushforward through a quasi-coherent subsheaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A nonzero global function on the source of a flat, locally finitely presented,
locally quasi-finite morphism remains nonzero over compatible opens and factors through
a monomorphism from a positive finite biproduct of a quasi-coherent subsheaf. -/
theorem exists_open_subsheaf_embedding {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [LocallyQuasiFinite f]
    (g : Γ(X, ⊤)) (hg : g ≠ 0) :
    ∃ (V : X.Opens) (U : S.Opens) (π : V.toScheme ⟶ U.toScheme),
      V.ι.appTop g ≠ 0 ∧
      π ≫ U.ι = V.ι ≫ f ∧
      ∃ (F : Subobject
          (SheafOfModules.unit U.toScheme.ringCatSheaf : U.toScheme.Modules))
        (r : ℕ), 0 < r ∧
        (Subobject.underlying.obj F : U.toScheme.Modules).IsQuasicoherent ∧
        ∃ (φ : (∐ fun _ : Fin r ↦
            (Subobject.underlying.obj F : U.toScheme.Modules)) ⟶
            π.pushforwardStructureModule),
          Mono φ ∧
          ∃ lift :
              (SheafOfModules.unit U.toScheme.ringCatSheaf : U.toScheme.Modules) ⟶
                (∐ fun _ : Fin r ↦
                  (Subobject.underlying.obj F : U.toScheme.Modules)),
            lift ≫ φ =
              SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom ≫
                (Scheme.Modules.pushforward π).map
                  (RingedSpace.topSectionMorphism
                    (SheafOfModules.unit V.toScheme.ringCatSheaf : V.toScheme.Modules)
                    (V.ι.appTop g)) := sorry

end AlgebraicGeometry.Scheme.Hom
