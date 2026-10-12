/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal Hom and stalks of module sheaves

This file owns the canonical comparison from the stalk of a sheaf internal Hom to the internal
Hom of the two stalk modules.  The comparison is explicit data; finite type gives injectivity and
finite presentation gives an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.InternalHom.Stalk

variable {X : RingedSpace.{u}}

/-- The stalk of the sheaf internal Hom from `F` to `G`. -/
abbrev source (F G : X.Modules) (x : X) :
    ModuleCat (X.presheaf.stalk x) :=
  RingedSpace.stalkModuleCat ((ihom F).obj G) x

/-- The internal Hom from the stalk of `F` to the stalk of `G`. -/
abbrev target (F G : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  (ihom (RingedSpace.stalkModuleCat F x)).obj (RingedSpace.stalkModuleCat G x)

/-- The canonical comparison from the stalk of a sheaf internal Hom to the internal Hom of the
stalk modules. -/
@[stacks 01CP "canonical comparison morphism"]
noncomputable def comparison (F G : X.Modules) (x : X) :
    source F G x ⟶ target F G x :=
  MonoidalClosed.curry
    (RingedSpace.Tensor.Stalk.comparisonInv F ((ihom F).obj G) x ≫
      RingedSpace.moduleStalkHom x ((ihom.ev F).app G))

/-- Uncurrying `comparison` gives stalkwise evaluation after transport across the tensor-stalk
comparison. -/
theorem uncurry_comparison (F G : X.Modules) (x : X) :
    MonoidalClosed.uncurry (comparison F G x) =
      RingedSpace.Tensor.Stalk.comparisonInv F ((ihom F).obj G) x ≫
        RingedSpace.moduleStalkHom x ((ihom.ev F).app G) := sorry

/-- Lemma 17.22.4 (01CP), finite-type clause: the internal-Hom stalk comparison is injective
when its source module sheaf is of finite type. -/
@[stacks 01CP "finite-type injectivity"]
theorem comparison_injective (F G : X.Modules) (x : X)
    [F.IsFiniteType] :
    Function.Injective (comparison F G x).hom := sorry

/-- The finite-type internal-Hom stalk comparison is a monomorphism in the module category. -/
@[stacks 01CP "finite-type monomorphism", instance]
instance comparison_mono (F G : X.Modules) (x : X)
    [F.IsFiniteType] :
    Mono (comparison F G x) := sorry

/-- Lemma 17.22.4 (01CP), finite-presentation clause: the internal-Hom stalk comparison is an
isomorphism when its source module sheaf is finitely presented. -/
@[stacks 01CP "finite-presentation isomorphism", instance]
instance comparison_isIso (F G : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    IsIso (comparison F G x) := sorry

/-- The named inverse of the internal-Hom stalk comparison for a finitely presented source
module sheaf. -/
@[stacks 01CP "finite-presentation inverse comparison"]
noncomputable def comparisonInv (F G : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    target F G x ⟶ source F G x :=
  inv (comparison F G x)

/-- The internal-Hom stalk comparison followed by its named inverse is the identity. -/
@[simp, stacks 01CP "finite-presentation forward-inverse comparison law"]
theorem comparison_hom_inv_id (F G : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    comparison F G x ≫ comparisonInv F G x = 𝟙 _ := sorry

/-- The named inverse followed by the internal-Hom stalk comparison is the identity. -/
@[simp, stacks 01CP "finite-presentation inverse-forward comparison law"]
theorem comparison_inv_hom_id (F G : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    comparisonInv F G x ≫ comparison F G x = 𝟙 _ := sorry

/-- The internal-Hom stalk comparison as an explicit isomorphism for a finitely presented
source module sheaf. -/
@[stacks 01CP "finite-presentation comparison isomorphism"]
noncomputable def comparisonIso (F G : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    source F G x ≅ target F G x where
  hom := comparison F G x
  inv := comparisonInv F G x
  hom_inv_id := comparison_hom_inv_id F G x
  inv_hom_id := comparison_inv_hom_id F G x

/-- The forward map of the internal-Hom stalk comparison isomorphism. -/
@[stacks 01CP "finite-presentation comparison isomorphism hom", simp]
theorem comparisonIso_hom (F G : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    (comparisonIso F G x).hom = comparison F G x := sorry

/-- The inverse map of the internal-Hom stalk comparison isomorphism is `comparisonInv`. -/
@[stacks 01CP "finite-presentation comparison isomorphism inverse", simp]
theorem comparisonIso_inv (F G : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    (comparisonIso F G x).inv = comparisonInv F G x := sorry

/-- The internal-Hom stalk comparison is natural in its target module. -/
@[stacks 01CP "internal-Hom stalk comparison naturality"]
theorem comparison_naturality (F : X.Modules) {G H : X.Modules}
    (g : G ⟶ H) (x : X) :
    RingedSpace.moduleStalkHom x ((ihom F).map g) ≫ comparison F H x =
      comparison F G x ≫
        (ihom (RingedSpace.stalkModuleCat F x)).map
          (RingedSpace.moduleStalkHom x g) := sorry

/-- The named inverse internal-Hom stalk comparison is natural in its target module. -/
@[stacks 01CP "inverse internal-Hom stalk comparison naturality"]
theorem comparisonInv_naturality (F : X.Modules) {G H : X.Modules}
    [F.IsFinitePresentation] (g : G ⟶ H) (x : X) :
    (ihom (RingedSpace.stalkModuleCat F x)).map
          (RingedSpace.moduleStalkHom x g) ≫ comparisonInv F H x =
      comparisonInv F G x ≫
        RingedSpace.moduleStalkHom x ((ihom F).map g) := sorry

/-- The internal-Hom stalk comparison is contravariantly natural in its source module. -/
@[stacks 01CP "internal-Hom stalk comparison left naturality"]
theorem comparison_naturality_left {E F : X.Modules} (g : E ⟶ F)
    (G : X.Modules) (x : X) :
    comparison F G x ≫
        (MonoidalClosed.pre (RingedSpace.moduleStalkHom x g)).app
          (RingedSpace.stalkModuleCat G x) =
      RingedSpace.moduleStalkHom x ((MonoidalClosed.pre g).app G) ≫ comparison E G x := sorry

/-- The source functor for the internal-Hom stalk comparison with fixed source `F`. -/
@[stacks 01CP "internal-Hom stalk comparison source functor"]
noncomputable def sourceFunctor (F : X.Modules) (x : X) :
    X.Modules ⥤ ModuleCat (X.presheaf.stalk x) :=
  ihom F ⋙ RingedSpace.stalkModuleFunctor x

/-- The target functor for the internal-Hom stalk comparison with fixed source `F`. -/
@[stacks 01CP "internal-Hom stalk comparison target functor"]
noncomputable def targetFunctor (F : X.Modules) (x : X) :
    X.Modules ⥤ ModuleCat (X.presheaf.stalk x) :=
  RingedSpace.stalkModuleFunctor x ⋙ ihom (RingedSpace.stalkModuleCat F x)

/-- The internal-Hom stalk comparisons form a natural transformation in the target module. -/
@[stacks 01CP "internal-Hom stalk natural transformation"]
noncomputable def natTrans (F : X.Modules) (x : X) :
    sourceFunctor F x ⟶ targetFunctor F x where
  app G := comparison F G x
  naturality _ _ g := comparison_naturality F g x

/-- For a finitely presented source, the named inverse comparisons form a natural
transformation in the target module. -/
@[stacks 01CP "internal-Hom stalk inverse natural transformation"]
noncomputable def comparisonInvNatTrans (F : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    targetFunctor F x ⟶ sourceFunctor F x where
  app G := comparisonInv F G x
  naturality _ _ g := comparisonInv_naturality F g x

/-- A component of `natTrans` is the canonical internal-Hom stalk comparison. -/
@[stacks 01CP "internal-Hom stalk comparison natural transformation component", simp]
theorem natTrans_app (F G : X.Modules) (x : X) :
    (natTrans F x).app G = comparison F G x := sorry

/-- The comparison natural transformation followed by its named inverse is the identity. -/
@[simp, stacks 01CP "internal-Hom stalk natural forward-inverse law"]
theorem natTrans_hom_inv_id (F : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    natTrans F x ≫ comparisonInvNatTrans F x = 𝟙 _ := sorry

/-- The named inverse followed by the comparison natural transformation is the identity. -/
@[simp, stacks 01CP "internal-Hom stalk natural inverse-forward law"]
theorem natTrans_inv_hom_id (F : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    comparisonInvNatTrans F x ≫ natTrans F x = 𝟙 _ := sorry

/-- For a finitely presented source, the internal-Hom stalk comparisons form a natural
isomorphism in the target module. -/
@[stacks 01CP "internal-Hom stalk natural isomorphism"]
noncomputable def comparisonNatIso (F : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    sourceFunctor F x ≅ targetFunctor F x where
  hom := natTrans F x
  inv := comparisonInvNatTrans F x
  hom_inv_id := natTrans_hom_inv_id F x
  inv_hom_id := natTrans_inv_hom_id F x

/-- Finite presentation makes the whole target-variable stalk comparison invertible. -/
@[stacks 01CP "internal-Hom stalk natural transformation isomorphism", instance]
noncomputable instance natTrans_isIso (F : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    IsIso (natTrans F x) := sorry

/-- The forward natural transformation of `comparisonNatIso` is the canonical comparison family. -/
@[stacks 01CP "internal-Hom stalk natural isomorphism hom", simp]
theorem comparisonNatIso_hom (F : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    (comparisonNatIso F x).hom = natTrans F x := sorry

/-- The inverse natural transformation of `comparisonNatIso` is the named inverse family. -/
@[stacks 01CP "internal-Hom stalk natural isomorphism inverse", simp]
theorem comparisonNatIso_inv (F : X.Modules) (x : X)
    [F.IsFinitePresentation] :
    (comparisonNatIso F x).inv = comparisonInvNatTrans F x := sorry

/-- A component of `comparisonNatIso` is the pointwise internal-Hom stalk isomorphism. -/
@[stacks 01CP "internal-Hom stalk natural isomorphism component", simp]
theorem comparisonNatIso_app (F : X.Modules) (x : X)
    [F.IsFinitePresentation] (G : X.Modules) :
    (comparisonNatIso F x).app G = comparisonIso F G x := sorry

/-- The forward component of `comparisonNatIso` is the canonical stalk comparison. -/
@[stacks 01CP "internal-Hom stalk natural isomorphism hom component", simp]
theorem comparisonNatIso_hom_app (F : X.Modules) (x : X)
    [F.IsFinitePresentation] (G : X.Modules) :
    (comparisonNatIso F x).hom.app G = comparison F G x := sorry

/-- The inverse component of `comparisonNatIso` is the named pointwise comparison inverse. -/
@[stacks 01CP "internal-Hom stalk natural isomorphism inverse component", simp]
theorem comparisonNatIso_inv_app (F : X.Modules) (x : X)
    [F.IsFinitePresentation] (G : X.Modules) :
    (comparisonNatIso F x).inv.app G = comparisonInv F G x := sorry

end AlgebraicGeometry.RingedSpace.InternalHom.Stalk

-- The named inverse is the categorical inverse selected by the finite-presentation
-- `comparison_isIso` gate, so it inherits that gate's current proof debt.  The pointwise and
-- natural isomorphisms are literal records built from this single owner; neither uses `asIso`
-- nor selects a second inverse.
