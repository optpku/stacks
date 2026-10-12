/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_20_2_Affine

/-!
# Pushforward as a module over the pushed-forward structure sheaf

A morphism `f : X ⟶ Y` of algebraic spaces induces the ring sheaf `A = f_* 𝒪_X` on the
small étale site of `Y`, together with the `A`-module-valued direct image of sheaves of
modules. For an affine morphism this restricts to an equivalence on quasi-coherent modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The ring sheaf `A = f_* 𝒪_X` on the small étale site of `Y`. -/
noncomputable def pushforwardStructureAlgebra (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) RingCat.{u} :=
  (ringedToposHom f).toTopos.ringDirectImage.obj (structureSheaf X)

/-- The algebra sheaf `pushforwardStructureAlgebra f` is the ring-valued direct image of `𝒪_X`. -/
theorem pushforwardStructureAlgebra_eq (f : X ⟶ Y) :
    pushforwardStructureAlgebra f =
      (ringedToposHom f).toTopos.ringDirectImage.obj (structureSheaf X) :=
  rfl

/-- The category of quasi-coherent modules over `f_* 𝒪_X`. -/
abbrev pushforwardAlgebraQCoh (f : X ⟶ Y) :=
  (SheafOfModules.isQuasicoherent (pushforwardStructureAlgebra f)).FullSubcategory

namespace Modules

/-- Direct image of module sheaves, retaining the natural module structure over `f_* 𝒪_X`. -/
noncomputable def pushforwardAsModule (f : X ⟶ Y) :
    X.Modules ⥤ SheafOfModules (pushforwardStructureAlgebra f) :=
  (ringedToposHom f).toTopos.moduleDirectImage (structureSheaf X)

/-- The `A`-module-valued pushforward is the presentation-independent module direct image. -/
theorem pushforwardAsModule_eq (f : X ⟶ Y) :
    pushforwardAsModule f =
      (ringedToposHom f).toTopos.moduleDirectImage (structureSheaf X) :=
  rfl

/-- Restricting scalars along `𝒪_Y ⟶ f_* 𝒪_X` recovers the ordinary module pushforward. -/
theorem pushforwardAsModule_restrictScalars (f : X ⟶ Y) :
    pushforwardAsModule f ⋙
        SheafOfModules.restrictScalars (ringedToposHom f).directStructureMap =
      pushforward f :=
  rfl

end Modules

namespace QCoh

namespace pushforwardAsModule

/-- Direct image as a module over `f_* 𝒪_X` sends quasi-coherent modules to quasi-coherent
`A`-modules along an affine morphism. -/
theorem mapsTo (f : X ⟶ Y) [Affine f] :
    quasiCoherentModuleProperty X ≤
      (SheafOfModules.isQuasicoherent (pushforwardStructureAlgebra f)).inverseImage
        (Modules.pushforwardAsModule f) :=
  sorry

end pushforwardAsModule

/-- Direct image from quasi-coherent `𝒪_X`-modules to quasi-coherent modules over `f_* 𝒪_X`. -/
noncomputable def pushforwardAsModule (f : X ⟶ Y) [Affine f] :
    QCoh X ⥤ pushforwardAlgebraQCoh f :=
  FullSubcategory.restrict (Modules.pushforwardAsModule f) (pushforwardAsModule.mapsTo f)

namespace pushforwardAsModule

/-- Forgetting quasi-coherence after `A`-module-valued direct image recovers the ambient functor. -/
noncomputable def inclusionIso (f : X ⟶ Y) [Affine f] :
    QCoh.pushforwardAsModule f ⋙
        (SheafOfModules.isQuasicoherent (pushforwardStructureAlgebra f)).ι ≅
      QCoh.inclusion X ⋙ Modules.pushforwardAsModule f :=
  FullSubcategory.restrict.compιIso (Modules.pushforwardAsModule f) (mapsTo f)

/-- For an affine morphism, direct image is an equivalence from quasi-coherent `𝒪_X`-modules
to quasi-coherent modules over `f_* 𝒪_X`. -/
instance isEquivalence (f : X ⟶ Y) [Affine f] :
    Functor.IsEquivalence (QCoh.pushforwardAsModule f) :=
  sorry

end pushforwardAsModule

end QCoh

namespace Modules

/-- An `A`-module is quasi-coherent as an `𝒪_Y`-module if and only if it is quasi-coherent as an
`A`-module, when `A = f_* 𝒪_X` for an affine morphism `f`. -/
theorem isQuasicoherent_iff (f : X ⟶ Y) [Affine f]
    (ℱ : SheafOfModules (pushforwardStructureAlgebra f)) :
    ((SheafOfModules.restrictScalars (ringedToposHom f).directStructureMap).obj ℱ).IsQuasicoherent ↔
      ℱ.IsQuasicoherent :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
