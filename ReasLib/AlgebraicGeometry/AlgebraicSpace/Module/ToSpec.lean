module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Associated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison

/-! # Absolute direct image to the spectrum of global sections -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TypeCat TopCat AlgebraicGeometry
open TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

/-- Direct image from the etale module site of a representable algebraic space to
the Zariski module site of its underlying scheme. -/
noncomputable def toScheme {S : Scheme.{u}} (U : Over S) :
    (ofOver U).Modules ⥤ U.left.Modules :=
  (schemeEtaleRingedHom U).modulePushforward.{u} ⋙
    (smallEtaleToOpensRingedHom U.left).modulePushforward.{u} ⋙
      opensToSchemeModules U.left

end Modules

/-- Absolute direct image to Spec A: graph direct image, etale-to-Zariski
direct image, then direct image along the scheme projection. -/
noncomputable def toSpecAPushforward {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.Modules ⥤ (Spec (globalSectionsRing X)).Modules :=
  Modules.pushforward (toSpecGamma X) ⋙ Modules.toScheme (specGammaOver X) ⋙
    Scheme.Modules.pushforward (specGamma_fst X)

/-- Global sections with the A-action supplied by the actual absolute map
to Spec A and Mathlib's affine module global-sections functor. -/
noncomputable def moduleGlobalSections {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : X.Modules) : ModuleCat.{u} (globalSectionsRing X) :=
  (moduleSpecΓFunctor (R := globalSectionsRing X)).obj ((toSpecAPushforward X).obj F)

/-- The etale object selected by the inverse image of the whole Spec A
under the projection and the two explicit site comparison functors. -/
private noncomputable def specAGlobalEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleSite (specGamma X) :=
  (schemeEtaleRingedHom (specGammaOver X)).base.obj
    ((smallEtaleToOpensRingedHom (specGammaOver X).left).base.obj
      ((specGamma_fst X) ⁻¹ᵁ ⊤))

/-- Evaluate the direct image of a compatible section at the open pulled
back from the whole Spec A, through the two explicit site comparison functors. -/
@[no_expose] noncomputable def toSpecAGlobalSection {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : X.Modules) (s : F.sections) : moduleGlobalSections X F :=
  (moduleDirectImageSection (toSpecGamma X) F s).1 (op (specAGlobalEtale X))

private theorem tensorOXSectionsUnit_map_add {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) (m n : M) :
    toSpecAGlobalSection X (tensorOX X M) (tensorOXUnitSection X M (m + n)) =
      toSpecAGlobalSection X (tensorOX X M) (tensorOXUnitSection X M m) +
      toSpecAGlobalSection X (tensorOX X M) (tensorOXUnitSection X M n) :=
  sorry

private theorem tensorOXSectionsUnit_map_smul {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) (r : globalSectionsRing X) (m : M) :
    toSpecAGlobalSection X (tensorOX X M) (tensorOXUnitSection X M (r • m)) =
      r • toSpecAGlobalSection X (tensorOX X M) (tensorOXUnitSection X M m) :=
  sorry

/-- The canonical A-linear comparison m maps to the compatible sections
1 tensor m, followed by actual direct image to Spec A and top-open evaluation. -/
noncomputable def tensorOXSectionsUnit {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) :
    M ⟶ moduleGlobalSections X (tensorOX X M) :=
  @ModuleCat.ofHom (globalSectionsRing X) _ M (moduleGlobalSections X (tensorOX X M))
    M.isAddCommGroup M.isModule
    (moduleGlobalSections X (tensorOX X M)).isAddCommGroup
    (moduleGlobalSections X (tensorOX X M)).isModule
    { toFun := fun m ↦ toSpecAGlobalSection X (tensorOX X M) (tensorOXUnitSection X M m)
      map_add' := by exact tensorOXSectionsUnit_map_add X M
      map_smul' := by exact tensorOXSectionsUnit_map_smul X M }

/-- The section comparison evaluates a module element by taking its canonical
associated-module section and applying absolute direct image. -/
theorem tensorOXSectionsUnit_apply {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) (m : M) :
    (tensorOXSectionsUnit X M).hom m =
      toSpecAGlobalSection X (tensorOX X M) (tensorOXUnitSection X M m) :=
  rfl

/-- The comparison tilde M to p_*(M tensor O_X) is the transpose of the
specified section map under Mathlib's proved tilde-global-sections adjunction. -/
noncomputable def tensorOXPushforwardUnit {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : ModuleCat.{u} (globalSectionsRing X)) :
    ((AlgebraicGeometry.tilde.functor (globalSectionsRing X)).obj M) ⟶ (toSpecAPushforward X).obj (tensorOX X M) :=
  ((AlgebraicGeometry.tilde.adjunction (R := globalSectionsRing X)).homEquiv M
    ((toSpecAPushforward X).obj (tensorOX X M))).symm (tensorOXSectionsUnit X M)

end AlgebraicGeometry.AlgebraicSpace
