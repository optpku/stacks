module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTransport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

/-! # Restriction to fibres and the canonical stalk-to-fibre map -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {Y : Scheme.{u}} {X : AlgebraicSpace Y}

/-- The pullback of a module on `X` to the scheme-theoretic fibre over `y`. -/
def fiberModule (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (F : X.Modules) (y : Y) :
    (fiber f y).Modules :=
  (pullback (fiberι f y)).obj F

/-- `fiberModule f F y` is module pullback along `fiberι f y`. -/
theorem fiberModule_eq (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (F : X.Modules) (y : Y) :
    fiberModule f F y = (pullback (fiberι f y)).obj F :=
  rfl

/-- The Zariski module on a representing scheme of the fibre obtained by transporting
`fiberModule` along the representing isomorphism. -/
def moduleOnScheme (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T) (F : X.Modules) : T.left.Modules :=
  toSchemeModule e (fiberModule f F y)

/-- `moduleOnScheme f y e F` is `toScheme` of the pullback of `fiberModule` along `e.inv`. -/
theorem moduleOnScheme_eq (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T) (F : X.Modules) :
    moduleOnScheme f y e F =
      (toScheme T).obj ((pullback e.inv).obj (fiberModule f F y)) :=
  rfl

/-- Pullback along the fibre projection preserves invertibility of modules. -/
instance instIsInvertibleObject_fiberModule (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    (L : X.Modules) [isInvertibleObject L] (y : Y) :
    isInvertibleObject (fiberModule f L y) :=
  isInvertibleObject_pullback (fiberι f y) L

/-- Transport of an invertible module on `X` to a representing scheme of the fibre is
invertible. -/
instance instInvertible_moduleOnScheme (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y)
    {T : Over Y} (e : fiber f y ≅ ofOver T) (L : X.Modules) [isInvertibleObject L] :
    Scheme.Modules.Invertible (moduleOnScheme f y e L) :=
  sorry

/-- The Zariski sheaf on `Y` associated to a higher direct image of an étale module. -/
def higherDirectImageOnScheme (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules] (G : X.Modules) (p : ℕ) :
    Y.Modules :=
  (toScheme (Over.mk (𝟙 Y))).obj (higherDirectImage f G p)

/-- `higherDirectImageOnScheme f G p` is `toScheme` of `higherDirectImage f G p`. -/
theorem higherDirectImageOnScheme_eq (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules] (G : X.Modules) (p : ℕ) :
    higherDirectImageOnScheme f G p =
      (toScheme (Over.mk (𝟙 Y))).obj (higherDirectImage f G p) :=
  rfl

/-- The morphism of algebraic spaces from a representing scheme of the fibre into `X`. -/
def fiberSchemeι (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T) : ofOver T ⟶ X :=
  e.inv ≫ fiberι f y

/-- `fiberSchemeι f y e` is `e.inv ≫ fiberι f y`. -/
theorem fiberSchemeι_eq (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T) :
    fiberSchemeι f y e = e.inv ≫ fiberι f y :=
  rfl

/-- The representing isomorphism identifies the composite `fiberSchemeι ≫ f` with the
structure morphism of `T`. -/
theorem fiberSchemeι_comp_eq (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T) :
    fiberSchemeι f y e ≫ f = overHomToBase T :=
  sorry

/-- Restriction of `G` along the fibre projection, as the unit of module pullback ⊣
pushforward. -/
def restrictToFiberUnit (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (G : X.Modules) (y : Y)
    {T : Over Y} (e : fiber f y ≅ ofOver T) :
    G ⟶ (pushforward (fiberSchemeι f y e)).obj
      ((pullback (fiberSchemeι f y e)).obj G) :=
  (pullbackPushforwardAdjunction (fiberSchemeι f y e)).unit.app G

/-- `restrictToFiberUnit` is the adjunction unit along `fiberSchemeι`. -/
theorem restrictToFiberUnit_eq (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (G : X.Modules) (y : Y)
    {T : Over Y} (e : fiber f y ≅ ofOver T) :
    restrictToFiberUnit f G y e =
      (pullbackPushforwardAdjunction (fiberSchemeι f y e)).unit.app G :=
  rfl

/-- Pushforward of the fibre-restriction unit, as a morphism of étale modules on `Y`. -/
def pushforwardRestrictToFiber (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules] (G : X.Modules) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T) :
    higherDirectImage f G 0 ⟶
      (pushforward (fiberSchemeι f y e ≫ f)).obj
        ((pullback (fiberSchemeι f y e)).obj G) :=
  (pushforward f).rightDerivedZeroIsoSelf.hom.app G ≫
    (pushforward f).map (restrictToFiberUnit f G y e) ≫
    (pushforwardComp (fiberSchemeι f y e) f).hom.app
      ((pullback (fiberSchemeι f y e)).obj G)

/-- `pushforwardRestrictToFiber` is `R^0 f_*` compared with underived pushforward of the
fibre-restriction unit. -/
theorem pushforwardRestrictToFiber_eq (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules] (G : X.Modules) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T) :
    pushforwardRestrictToFiber f G y e =
      (pushforward f).rightDerivedZeroIsoSelf.hom.app G ≫
        (pushforward f).map (restrictToFiberUnit f G y e) ≫
        (pushforwardComp (fiberSchemeι f y e) f).hom.app
          ((pullback (fiberSchemeι f y e)).obj G) :=
  rfl

/-- Restriction of `G` along the fibre projection, as a morphism of Zariski modules on `Y`
into the pushforward of `moduleOnScheme`. -/
def restrictToFiberOnScheme (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules] (G : X.Modules) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T) :
    higherDirectImageOnScheme f G 0 ⟶
      (Scheme.Modules.pushforward T.hom).obj (moduleOnScheme f y e G) :=
  (toScheme (Over.mk (𝟙 Y))).map (pushforwardRestrictToFiber f G y e) ≫
    eqToHom
      (congrArg
        (fun h : ofOver T ⟶ ofOver (Over.mk (𝟙 Y)) =>
          (toScheme (Over.mk (𝟙 Y))).obj
            ((pushforward h).obj ((pullback (fiberSchemeι f y e)).obj G)))
        (fiberSchemeι_comp_eq f y e)) ≫
    (toScheme (Over.mk (𝟙 Y))).map
      ((pushforward (overHomToBase T)).map
        ((pullbackCompIso e.inv (fiberι f y)).inv.app G)) ≫
    toSchemePushforwardHomOver T ((pullback e.inv).obj (fiberModule f G y))

/-- Pushforward of scheme modules evaluates on an open by preimage. -/
theorem pushforward_moduleSectionsOnOpen {Z : Scheme.{u}} (g : Z ⟶ Y) (M : Z.Modules)
    (U : Y.Opens) :
    RingedSpace.moduleSectionsOnOpen ((Scheme.Modules.pushforward g).obj M) U =
      RingedSpace.moduleSectionsOnOpen M (g ⁻¹ᵁ U) :=
  rfl

/-- The scheme-theoretic fibre, as a scheme over `Y`, lies over every open neighborhood of
the base point. -/
theorem fiberScheme_preimage_eq_top (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (y : Y)
    {T : Over Y} (e : fiber f y ≅ ofOver T) (U : Y.Opens) (hy : y ∈ U) :
    T.hom ⁻¹ᵁ U = ⊤ :=
  sorry

/-- Restriction of a neighborhood section of `f_* G` along the fibre projection to global
sections of `moduleOnScheme`. -/
def sectionsToFiber (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules] (G : X.Modules) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T) (U : Y.Opens) (hy : y ∈ U) :
    RingedSpace.moduleSectionsOnOpen (higherDirectImageOnScheme f G 0) U ⟶
      RingedSpace.moduleGlobalSections (moduleOnScheme f y e G) :=
  RingedSpace.Modules.Hom.app (restrictToFiberOnScheme f G y e) U ≫
    eqToHom
      (pushforward_moduleSectionsOnOpen T.hom (moduleOnScheme f y e G) U) ≫
    (moduleOnScheme f y e G).val.presheaf.map
      (homOfLE (le_of_eq (fiberScheme_preimage_eq_top f y e U hy).symm)).op

/-- The canonical map from the stalk of `f_* G` at `y` to global sections of the
restricted module on a representing scheme of the fibre. -/
def pushforwardStalkToFiberCohomology (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules] (G : X.Modules) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (higherDirectImageOnScheme f G 0).val.presheaf y ⟶
    RingedSpace.moduleGlobalSections (moduleOnScheme f y e G) :=
  colimit.desc _
    { pt := RingedSpace.moduleGlobalSections (moduleOnScheme f y e G)
      ι :=
        { app := fun U => sectionsToFiber f G y e U.unop.1 U.unop.2
          naturality := fun _ _ _ => sorry } }

/-- `pushforwardStalkToFiberCohomology` is restriction of neighborhood sections along
the fibre projection. -/
theorem sectionsToFiber_eq (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules] (G : X.Modules) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T) (U : Y.Opens) (hy : y ∈ U) :
    sectionsToFiber f G y e U hy =
      RingedSpace.Modules.Hom.app (restrictToFiberOnScheme f G y e) U ≫
        eqToHom
          (pushforward_moduleSectionsOnOpen T.hom (moduleOnScheme f y e G) U) ≫
        (moduleOnScheme f y e G).val.presheaf.map
          (homOfLE (le_of_eq (fiberScheme_preimage_eq_top f y e U hy).symm)).op :=
  rfl

/-- On a germ represented over a neighborhood `U` of `y`, `pushforwardStalkToFiberCohomology`
is `sectionsToFiber`. -/
theorem pushforwardStalkToFiberCohomology_germ (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules] (G : X.Modules) (y : Y) {T : Over Y}
    (e : fiber f y ≅ ofOver T) (U : Y.Opens) (hy : y ∈ U)
    (s : RingedSpace.moduleSectionsOnOpen (higherDirectImageOnScheme f G 0) U) :
    pushforwardStalkToFiberCohomology f G y e
        (TopCat.Presheaf.germ (higherDirectImageOnScheme f G 0).val.presheaf U y hy
          s) =
      sectionsToFiber f G y e U hy s :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
