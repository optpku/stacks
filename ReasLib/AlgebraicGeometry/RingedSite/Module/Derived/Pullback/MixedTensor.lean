module

public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Composition.KFlat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.TensorAction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Mixed derived tensor products for a morphism of ringed sites

For a morphism `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)`, pullback factors through modules over
`f⁻¹𝒪_Y`: first take inverse image and then extend scalars along
`f⁻¹𝒪_Y ⟶ 𝒪_X`.  Tensoring an `𝒪_X`-module with the resulting extension of
scalars is the canonical derived model of the mixed tensor product over `f⁻¹𝒪_Y`.

The concrete comparison data is built for the displayed factorization.  Its equality with the
original bundled morphism is kept as a separate proposition, so no `Iso` data depends on a
deferred equality proof.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom.PullbackFactorization

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(f.base.sheafPushforwardContinuous CommRingCat.{w} JY JX).IsRightAdjoint]

/-- The ringed-site morphism whose module pullback is inverse image from `Y` to modules over
`f⁻¹𝒪_Y` on `X`. -/
@[stacks 08I6 "inverse-image factor"]
abbrev inverseImage :
    RingedSite.Hom
      (RingedSite.ofCommRingSheaf JX (inverseImageStructureSheaf f))
      (RingedSite.ofCommRingSheaf JY OY) :=
  RingedSite.Hom.ofPullback (JC := JX) (JD := JY) f.base OY

/-- The same-site morphism whose module pullback extends scalars from `f⁻¹𝒪_Y` to
`𝒪_X`. -/
@[stacks 08I6 "scalar-extension factor"]
abbrev scalarExtension :
    RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
      (RingedSite.ofCommRingSheaf JX (inverseImageStructureSheaf f)) :=
  SheafOfModules.RingedSite.sameSiteHom (inverseImageStructureSheafMap f)

/-- The displayed factorization of a morphism of commutative ringed-site presentations into
inverse image followed by same-site scalar extension. -/
@[stacks 08I6 "pullback factorization"]
abbrev hom :
    RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
      (RingedSite.ofCommRingSheaf JY OY) :=
  (scalarExtension f).comp (inverseImage f)

/-- The displayed inverse-image/scalar-extension composite recovers the original bundled
ringed-site morphism. -/
@[stacks 08I6 "pullback factorization recovers the morphism"]
theorem hom_eq : hom f = f := sorry

end RingedSite.Hom.PullbackFactorization

namespace RingedSite.Hom.modulePullbackDerived.MixedTensor

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
  [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify JY AddCommGrpCat.{w}]
  [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [hX : UnivLE.{max uX vX, w}] [hY : UnivLE.{max uY vY, w}]
variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(f.base.sheafPushforwardContinuous CommRingCat.{w} JY JX).IsRightAdjoint]
variable [((PullbackFactorization.inverseImage f).modulePushforward.{w}).IsRightAdjoint]
variable [((PullbackFactorization.scalarExtension f).modulePushforward.{w}).IsRightAdjoint]
variable [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{w} (PullbackFactorization.scalarExtension f))
    (ModuleQis.{w}
      (RingedSite.ofCommRingSheaf JX (inverseImageStructureSheaf f)))]
variable [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{w} (PullbackFactorization.inverseImage f))
    (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))]
variable [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{w} (PullbackFactorization.hom f))
    (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))]
/-- Derived inverse image from `Y` to modules over `f⁻¹𝒪_Y` on `X`. -/
abbrev inverseImage :
    (@ModuleDerived.{w, uY, vY, w}
        (RingedSite.ofCommRingSheaf JY OY) hY) ⥤
      (@ModuleDerived.{w, uX, vX, w}
        (RingedSite.ofCommRingSheaf JX (inverseImageStructureSheaf f)) hX) :=
  modulePullbackDerived.{w} (PullbackFactorization.inverseImage f)

/-- Derived extension of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
abbrev scalarExtension :
    (@ModuleDerived.{w, uX, vX, w}
        (RingedSite.ofCommRingSheaf JX (inverseImageStructureSheaf f)) hX) ⥤
      (@ModuleDerived.{w, uX, vX, w}
        (RingedSite.ofCommRingSheaf JX OX) hX) :=
  modulePullbackDerived.{w} (PullbackFactorization.scalarExtension f)

/-- Derived pullback along the displayed inverse-image/scalar-extension composite. -/
abbrev pullback :
    (@ModuleDerived.{w, uY, vY, w}
        (RingedSite.ofCommRingSheaf JY OY) hY) ⥤
      (@ModuleDerived.{w, uX, vX, w}
        (RingedSite.ofCommRingSheaf JX OX) hX) :=
  modulePullbackDerived.TensorAction.composite
    (hX := hX) (hZ := hY)
    (PullbackFactorization.scalarExtension f)
    (PullbackFactorization.inverseImage f)

/-- The underlying derived-pullback composition comparison in the displayed factorization is
invertible.  It remains a theorem rather than inverse data during the statement stage. -/
@[stacks 08I6 "factorized derived pullback comparison is invertible"]
theorem compComparison_isIso :
    IsIso (modulePullbackDerived.compComparison
      (PullbackFactorization.scalarExtension f)
      (PullbackFactorization.inverseImage f)) := sorry

variable [@ModuleDerived.KFlat.HomotopyTensorDescends C _ JX _ _ _ hX OX]
variable [@ModuleDerived.KFlat.TensorDescends C _ JX _ _ _ hX OX _]
variable [@ModuleDerived.KFlat.IsLocalization C _ JX _ _ _ hX OX]

-- Local instance justification (defeq pin): the mixed tensor is over the displayed structure sheaf `OX`.
-- Fix its K-flat localization model instead of accepting an arbitrary monoidal structure.
local instance : MonoidalCategory
    (@ModuleDerived.{w, uX, vX, w} (RingedSite.ofCommRingSheaf JX OX) hX) :=
  @ModuleDerived.monoidalCategory C _ JX _ _ _ hX OX _ _ _

/-- The mixed derived tensor bifunctor over `f⁻¹𝒪_Y`, modeled by derived extension of
scalars followed by the canonical K-flat derived tensor product over `𝒪_X`. -/
@[stacks 08I6 "mixed derived tensor bifunctor"]
abbrev functor := Functor.tensorRightAction (scalarExtension f)

/-- The mixed derived tensor product of an `𝒪_X`-module and an `f⁻¹𝒪_Y`-module. -/
@[stacks 08I6 "mixed derived tensor product"]
abbrev obj
    (F : @ModuleDerived.{w, uX, vX, w}
      (RingedSite.ofCommRingSheaf JX OX) hX)
    (G : @ModuleDerived.{w, uX, vX, w}
      (RingedSite.ofCommRingSheaf JX (inverseImageStructureSheaf f)) hX) :=
  Functor.tensorRightActionObj (scalarExtension f) F G

/-- The canonical comparison from the mixed tensor action of iterated derived pullback to the
action of derived pullback along the displayed composite. -/
@[stacks 08I6 "mixed derived tensor comparison"]
def comparison := modulePullbackDerived.TensorAction.comparison
  (hX := hX) (hY := hX) (hZ := hY)
  (PullbackFactorization.scalarExtension f)
  (PullbackFactorization.inverseImage f)

variable [IsIso (modulePullbackDerived.compComparison
  (PullbackFactorization.scalarExtension f)
  (PullbackFactorization.inverseImage f))]

/-- Lemma 21.18.5 (08I6), bifunctorial factorized form: tensoring with derived pullback along
the displayed composite is canonically the mixed tensor over `f⁻¹𝒪_Y`. -/
@[stacks 08I6 "bifunctorial mixed derived tensor isomorphism"]
def natIso := modulePullbackDerived.TensorAction.natIso
  (hX := hX) (hY := hX) (hZ := hY)
  (PullbackFactorization.scalarExtension f)
  (PullbackFactorization.inverseImage f)

/-- Lemma 21.18.5 (08I6), pointwise factorized form:
`F ⊗ᴸ Lf⁺G ≅ F ⊗ᴸ_[f⁻¹𝒪_Y] f⁻¹G`. -/
@[stacks 08I6 "pointwise mixed derived tensor isomorphism"]
abbrev iso
    (F : @ModuleDerived.{w, uX, vX, w}
      (RingedSite.ofCommRingSheaf JX OX) hX)
    (G : @ModuleDerived.{w, uY, vY, w}
      (RingedSite.ofCommRingSheaf JY OY) hY) :
    Functor.tensorRightActionObj
        (pullback (hX := hX) (hY := hY) f) F G ≅
      obj (hX := hX) f F
        ((inverseImage (hX := hX) (hY := hY) f).obj G) :=
  modulePullbackDerived.TensorAction.iso
    (hX := hX) (hY := hX) (hZ := hY)
    (PullbackFactorization.scalarExtension f)
    (PullbackFactorization.inverseImage f) F G

end RingedSite.Hom.modulePullbackDerived.MixedTensor

-- The equality and invertibility results are Prop-valued proof debt.  The functor, comparison,
-- and conditional isomorphism data do not eliminate either deferred proof.
