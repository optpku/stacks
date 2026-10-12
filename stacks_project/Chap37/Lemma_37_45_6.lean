/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.QuasiFinite.NonzeroSection
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.45.6: a nonzero global function on the source of a flat, locally finitely
presented, locally quasi-finite morphism remains nonzero over suitable opens and factors
through a positive finite biproduct of a quasi-coherent subsheaf of the structure sheaf. -/
@[stacks 082V] #check
  (AlgebraicGeometry.Scheme.Hom.exists_open_subsheaf_embedding :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [Flat f] [LocallyOfFinitePresentation f] [LocallyQuasiFinite f]
      (g : Γ(X, ⊤)) (_hg : g ≠ 0),
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
                      (V.ι.appTop g)))
