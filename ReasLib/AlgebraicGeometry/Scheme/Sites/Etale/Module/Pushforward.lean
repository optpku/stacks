module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Composition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Sites.Continuous

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open RightDerived.Cochain
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Λ : Type u} [CommRing Λ]

/-- Transport of underived module pushforward along an equality of scheme
morphisms. -/
def etaleModulePushforwardCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    etaleModulePushforward f Λ ≅ etaleModulePushforward g Λ :=
  eqToIso (congrArg (fun u ↦ etaleModulePushforward u Λ) h)

section SheafTensor

variable (S : Scheme.{u})
  [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
  [(S.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]

/-- The canonical sheaf tensor inherits the symmetry of coefficient modules. -/
instance moduleSheafSymmetric :
    SymmetricCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  Sheaf.symmetricCategory S.smallEtaleTopology (ModuleCat.{u} Λ)

/-- Sheafification of the pointwise tensor of the underlying module presheaves is the sheaf
tensor product, through the canonical monoidal sheafification and its counit. -/
private def moduleSheafTensorIso
    (A B : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (presheafToSheaf S.smallEtaleTopology (ModuleCat.{u} Λ)).obj (A.obj ⊗ B.obj) ≅ A ⊗ B :=
  (Monoidal.μIso (presheafToSheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) A.obj B.obj).symm ≪≫
    tensorIso
      (sheafificationIso A).symm
      (sheafificationIso B).symm

variable {U V : Scheme.{u}}
  [HasSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify V.smallEtaleTopology (ModuleCat.{u} Λ)]
  [(U.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]
  [(V.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal]

/-- The ordinary direct-image tensor map is induced by the pointwise tensor map on sections
and the universal property of sheafification. -/
@[no_expose]
def modulePushforwardTensor (f : U ⟶ V)
    (A B : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleModulePushforward f Λ).obj A ⊗ (etaleModulePushforward f Λ).obj B ⟶
      (etaleModulePushforward f Λ).obj (A ⊗ B) :=
  (moduleSheafTensorIso V
      ((etaleModulePushforward f Λ).obj A) ((etaleModulePushforward f Λ).obj B)).inv ≫
    ((sheafificationAdjunction V.smallEtaleTopology (ModuleCat.{u} Λ)).homEquiv _ _).symm
      (Functor.whiskerLeft (smallEtalePullback f).op
        (((sheafificationAdjunction U.smallEtaleTopology
          (ModuleCat.{u} Λ)).rightAdjointLaxMonoidal).μ A B))

/-- The canonical inverse-image tensor map, as the mate of the sectionwise direct-image tensor
map. This fixes the normalization before passing to complexes or derived categories. -/
def modulePullbackTensor (f : U ⟶ V)
    {F : Sheaf V.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)}
    (adj : F ⊣ etaleModulePushforward f Λ)
    (A B : Sheaf V.smallEtaleTopology (ModuleCat.{u} Λ)) :
    F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B :=
  (adj.homEquiv _ _).symm
    ((adj.unit.app A ⊗ₘ adj.unit.app B) ≫
      modulePushforwardTensor f (F.obj A) (F.obj B))

end SheafTensor

/-- Inverse image of small-étale module sheaves, the canonical left adjoint to direct image. -/
abbrev etaleModuleInverseImage {U V : Scheme.{u}} (f : U ⟶ V)
    [(etaleModulePushforward f Λ).IsRightAdjoint] :
    Sheaf V.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ) :=
  (etaleModulePushforward f Λ).leftAdjoint

/-- The inverse-image/direct-image adjunction is the continuous sheaf adjunction. -/
def etaleModuleInverseImageAdjunction {U V : Scheme.{u}} (f : U ⟶ V)
    [(etaleModulePushforward f Λ).IsRightAdjoint] :
    etaleModuleInverseImage f (Λ := Λ) ⊣ etaleModulePushforward f Λ :=
  Adjunction.ofIsRightAdjoint (etaleModulePushforward f Λ)

/-- Continuous pushforward of small-étale module sheaves is additive whenever module
pushforward is additive. -/
instance etaleModulePushforwardContinuous_additive {U V : Scheme.{u}} (f : U ⟶ V)
    [(etaleModulePushforward f Λ).Additive] :
    ((smallEtalePullback f).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) V.smallEtaleTopology U.smallEtaleTopology).Additive :=
  inferInstanceAs (etaleModulePushforward f Λ).Additive


end AlgebraicGeometry.Scheme.Etale

end
