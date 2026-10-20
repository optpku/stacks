/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GeneralLinear.UnitFixing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree.Points
public import ReasLib.RingTheory.Algebra.FreeDimensional.Action

/-!
# The conjugation action of G on the universal free-algebra scheme

The conjugation formula `a(g, m) = g⁻¹ ∘ m ∘ (g ⊗ g)` is a right action
of `G`. We realize it as a left action of the opposite group algebraic space, so
that the action groupoid composes using the opposite product. The associated
quotient stack is `[X/G]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite CartesianMonoidalCategory MonoidalCategory
open AlgebraicGeometry.GroupAlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace
open scoped AlgebraicGeometry CategoryTheory.MonObj MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GLFixOne

/-- The universe-`u` model of the universal free-algebra base scheme. -/
def baseScheme (d : ℕ) [NeZero d] : Scheme.{u} :=
  Spec (CommRingCat.of (ULift.{u} (UniversalFiniteFreeAlgebra.CoefficientRing ⟨d, Nat.pos_of_neZero d⟩)))

/-- `baseScheme d` is the spectrum of the universe-lifted coefficient ring. -/
theorem baseScheme_eq (d : ℕ) [NeZero d] :
    baseScheme d =
      Spec (CommRingCat.of (ULift.{u} (UniversalFiniteFreeAlgebra.CoefficientRing ⟨d, Nat.pos_of_neZero d⟩))) :=
  rfl

/-- The universe-`u` model of the universal finite free family. -/
def familyScheme (d : ℕ) [NeZero d] : Scheme.{u} :=
  Spec (CommRingCat.of (ULift.{u} (UniversalFiniteFreeAlgebra.UniversalAlgebra ⟨d, Nat.pos_of_neZero d⟩)))

/-- The ring homomorphism underlying the universal projection, lifted to universe `u`. -/
def structureMapULift (d : ℕ) [NeZero d] :
    ULift.{u} (UniversalFiniteFreeAlgebra.CoefficientRing ⟨d, Nat.pos_of_neZero d⟩) →+*
      ULift.{u} (UniversalFiniteFreeAlgebra.UniversalAlgebra ⟨d, Nat.pos_of_neZero d⟩) :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((CommRingCat.Hom.hom
        (UniversalFiniteFreeAlgebra.structureMap ⟨d, Nat.pos_of_neZero d⟩)).comp
      ULift.ringEquiv.toRingHom)

/-- The universal finite free projection in universe `u`. -/
def projection (d : ℕ) [NeZero d] : familyScheme d ⟶ baseScheme d :=
  Spec.map (CommRingCat.ofHom (structureMapULift d))

/-- The universal projection is finite locally free of rank `d`. -/
instance instIsFiniteLocallyFreeOfRank_projection (d : ℕ) [NeZero d] :
    IsFiniteLocallyFreeOfRank (projection d) d :=
  sorry

/-- The universal free-algebra scheme as an object over `specZ`. -/
def baseOver (d : ℕ) [NeZero d] : Over specZ :=
  Over.mk (specULiftZIsTerminal.from (baseScheme d))

/-- The structure morphism of `baseOver d` is the unique map to `specZ`. -/
theorem baseOver_hom (d : ℕ) [NeZero d] :
    (baseOver d).hom = specULiftZIsTerminal.from (baseScheme d) :=
  rfl

/-- The universal free-algebra scheme as an algebraic space over `specZ`. -/
def baseSpaceLeft (d : ℕ) [NeZero d] : AlgebraicSpace specZ :=
  AlgebraicSpace.ofOver (baseOver d)

/-- The universal free-algebra scheme as an object of the slice over `base`. -/
def baseSpace (d : ℕ) [NeZero d] : Over base :=
  Over.mk (AlgebraicSpace.SchemeRealization.toBase (baseSpaceLeft d))

/-- `baseSpace d` is `Over.mk` of the unique morphism from `baseSpaceLeft d` to `base`. -/
theorem baseSpace_eq (d : ℕ) [NeZero d] :
    baseSpace d = Over.mk (AlgebraicSpace.SchemeRealization.toBase (baseSpaceLeft d)) :=
  rfl

/-- Morphisms `T ⟶ baseScheme d` correspond to ring maps out of the universal coefficient
ring into global sections. -/
def schemeHomCoeff (T : Scheme.{u}) (d : ℕ) [NeZero d] :
    (T ⟶ baseScheme d) ≃
      (UniversalFiniteFreeAlgebra.CoefficientRing ⟨d, Nat.pos_of_neZero d⟩ →+* Γ(T, ⊤)) where
  toFun f :=
    (CommRingCat.Hom.hom
        (Scheme.homToSpecGlobalSectionsEquiv T
          (CommRingCat.of
            (ULift.{u}
              (UniversalFiniteFreeAlgebra.CoefficientRing ⟨d, Nat.pos_of_neZero d⟩)))
          f)).comp
      ULift.ringEquiv.symm.toRingHom
  invFun ψ :=
    (Scheme.homToSpecGlobalSectionsEquiv T
        (CommRingCat.of
          (ULift.{u}
            (UniversalFiniteFreeAlgebra.CoefficientRing ⟨d, Nat.pos_of_neZero d⟩)))).symm
      (CommRingCat.ofHom (ψ.comp ULift.ringEquiv.toRingHom))
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `schemeHomCoeff` composes global sections with the universe-lift
equivalence. -/
theorem schemeHomCoeff_apply (T : Scheme.{u}) (d : ℕ) [NeZero d] (f : T ⟶ baseScheme d) :
    schemeHomCoeff T d f =
      (CommRingCat.Hom.hom
          (Scheme.homToSpecGlobalSectionsEquiv T
            (CommRingCat.of
              (ULift.{u}
                (UniversalFiniteFreeAlgebra.CoefficientRing ⟨d, Nat.pos_of_neZero d⟩)))
            f)).comp
        ULift.ringEquiv.symm.toRingHom :=
  rfl

/-- Morphisms `T ⟶ baseScheme d` correspond to free `d`-dimensional algebras over global
sections, via the universe-lifted coefficient ring. -/
def schemeHomEquiv (T : Scheme.{u}) (d : ℕ) [NeZero d] :
    (T ⟶ baseScheme d) ≃ FreeDimAlgebra Γ(T, ⊤) d :=
  (schemeHomCoeff T d).trans
    (UniversalFiniteFreeAlgebra.schemeHomFreeDimAlgebra T ⟨d, Nat.pos_of_neZero d⟩)

/-- The forward map of `schemeHomEquiv` classifies the free algebra of structure constants. -/
theorem schemeHomEquiv_apply (T : Scheme.{u}) (d : ℕ) [NeZero d] (f : T ⟶ baseScheme d) :
    schemeHomEquiv T d f =
      UniversalFiniteFreeAlgebra.schemeHomFreeDimAlgebra T ⟨d, Nat.pos_of_neZero d⟩
        (schemeHomCoeff T d f) :=
  rfl

/-- Convert a `T`-point of `baseSpaceLeft d` to a morphism of schemes over `specZ`. -/
def classifying {d : ℕ} [NeZero d] {T : Over specZ}
    (x : AlgebraicSpace.ofOver T ⟶ baseSpaceLeft d) : T ⟶ baseOver d :=
  yonedaEquiv x

/-- `classifying` is the Yoneda equivalent of a morphism of representable algebraic spaces. -/
theorem classifying_eq {d : ℕ} [NeZero d] {T : Over specZ}
    (x : AlgebraicSpace.ofOver T ⟶ baseSpaceLeft d) :
    classifying x = yonedaEquiv x :=
  rfl

/-- Convert a `T`-point of `space d` to a morphism of schemes over `specZ`. -/
def classifyingGroup {d : ℕ} [NeZero d] {T : Over specZ}
    (g : AlgebraicSpace.ofOver T ⟶ space d) : T ⟶ groupOver d :=
  yonedaEquiv g

/-- `classifyingGroup` is the Yoneda equivalent of a morphism of representable algebraic
spaces. -/
theorem classifyingGroup_eq {d : ℕ} [NeZero d] {T : Over specZ}
    (g : AlgebraicSpace.ofOver T ⟶ space d) :
    classifyingGroup g = yonedaEquiv g :=
  rfl

/-- The unit-fixing algebraic space in the slice over the integer base, equipped below
with opposite multiplication. -/
def asOverOp (d : ℕ) [NeZero d] : Over base :=
  Over.mk (AlgebraicSpace.SchemeRealization.toBase (space d))

/-- `asOverOp d` has underlying algebraic space `space d`. -/
theorem asOverOp_left (d : ℕ) [NeZero d] :
    (asOverOp d).left = space d :=
  rfl

/-- The unit section of `asOverOp d`. -/
def oneOp (d : ℕ) [NeZero d] : 𝟙_ (Over base) ⟶ asOverOp d :=
  Over.homMk (AlgebraicSpace.ofOverMap (η[groupOver d])) sorry

/-- The underlying algebraic-space map of `oneOp d` is `ofOverMap` of the scheme-level unit. -/
theorem oneOp_left (d : ℕ) [NeZero d] :
    (oneOp d).left = AlgebraicSpace.ofOverMap (η[groupOver d]) :=
  rfl

/-- The inverse morphism of `asOverOp d`. -/
def invOp (d : ℕ) [NeZero d] : asOverOp d ⟶ asOverOp d :=
  Over.homMk (AlgebraicSpace.ofOverMap (ι[groupOver d])) sorry

/-- The underlying algebraic-space map of `invOp d` is `ofOverMap` of the scheme-level inverse. -/
theorem invOp_left (d : ℕ) [NeZero d] :
    (invOp d).left = AlgebraicSpace.ofOverMap (ι[groupOver d]) :=
  rfl

/-- Opposite multiplication `(g, g') ↦ g' * g` on `asOverOp d`. -/
def mulOp (d : ℕ) [NeZero d] : asOverOp d ⊗ asOverOp d ⟶ asOverOp d :=
  Over.homMk
    (spaceMul (snd (asOverOp d) (asOverOp d)).left
      (fst (asOverOp d) (asOverOp d)).left)
    sorry

/-- The underlying algebraic-space map of `mulOp d` multiplies the swapped projections. -/
theorem mulOp_left (d : ℕ) [NeZero d] :
    (mulOp d).left =
      spaceMul (snd (asOverOp d) (asOverOp d)).left
        (fst (asOverOp d) (asOverOp d)).left :=
  rfl

/-- The opposite group-object structure on `asOverOp d`. -/
instance instGrpObj_asOverOp (d : ℕ) [NeZero d] : GrpObj (asOverOp d) where
  one := oneOp d
  mul := mulOp d
  inv := invOp d
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  left_inv := sorry
  right_inv := sorry

/-- The opposite unit-fixing group algebraic space, so that composition in the action
groupoid uses the order `(g' * g, m')`. -/
def groupSpaceOp (d : ℕ) [NeZero d] : GroupAlgebraicSpace base :=
  ⟨asOverOp d⟩

/-- The underlying object of `groupSpaceOp d` is `asOverOp d`. -/
theorem groupSpaceOp_X (d : ℕ) [NeZero d] : (groupSpaceOp d).X = asOverOp d :=
  rfl

/-- Morphisms over `base` into `groupSpaceOp d` are multiplicatively equivalent to
unit-fixing automorphisms, opposite to the usual product on `glFixOne`. -/
def pointsMulEquivOp (d : ℕ) [NeZero d] {T : Over specZ}
    (t : AlgebraicSpace.ofOver T ⟶ base) :
    (Over.mk t ⟶ (groupSpaceOp d).X) ≃* (glFixOne Γ(T.left, ⊤) d)ᵐᵒᵖ where
  toFun φ := MulOpposite.op (homEquiv d T (yonedaEquiv φ.left))
  invFun g :=
    Over.homMk (AlgebraicSpace.ofOverMap ((homEquiv d T).symm g.unop)) sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-- The forward map of `pointsMulEquivOp` is `MulOpposite.op` of `homEquiv`. -/
theorem pointsMulEquivOp_apply (d : ℕ) [NeZero d] {T : Over specZ}
    (t : AlgebraicSpace.ofOver T ⟶ base) (φ : Over.mk t ⟶ (groupSpaceOp d).X) :
    pointsMulEquivOp d t φ = MulOpposite.op (homEquiv d T (yonedaEquiv φ.left)) :=
  rfl

/-- The conjugation action of `G`-points on `X`-points. -/
def spaceAction {d : ℕ} [NeZero d] {E : AlgebraicSpace specZ}
    (g : E ⟶ space d) (x : E ⟶ baseSpaceLeft d) : E ⟶ baseSpaceLeft d where
  app T := ↾fun p ↦
    Over.homMk
      ((schemeHomEquiv T.unop.left d).symm
        (FreeDimAlgebra.conjugate (homEquiv d T.unop (g.app T p))
          (schemeHomEquiv T.unop.left d (x.app T p).left)))
      sorry
  naturality := sorry

/-- The action morphism `Gᵐᵒᵖ × X ⟶ X` over `base`. -/
def actionMap (d : ℕ) [NeZero d] :
    (groupSpaceOp d).X ⊗ baseSpace d ⟶ baseSpace d :=
  Over.homMk
    (spaceAction (fst (groupSpaceOp d).X (baseSpace d)).left
      ((snd (groupSpaceOp d).X (baseSpace d)).left))
    sorry

/-- The underlying algebraic-space map of `actionMap` is conjugation of points. -/
theorem actionMap_left (d : ℕ) [NeZero d] :
    (actionMap d).left =
      spaceAction (fst (groupSpaceOp d).X (baseSpace d)).left
        ((snd (groupSpaceOp d).X (baseSpace d)).left) :=
  rfl

/-- The left action of `groupSpaceOp d` on `baseSpace d`, with
`MulOpposite.op g • m = FreeDimAlgebra.conjugate g m` on points. -/
instance instModObj (d : ℕ) [NeZero d] :
    ModObj (groupSpaceOp d).X (baseSpace d) where
  smul := actionMap d
  one_smul := sorry
  mul_smul := sorry

/-- The bundled left action of `Gᵐᵒᵖ` on the universal free-algebra scheme. -/
def action (d : ℕ) [NeZero d] : Action (groupSpaceOp d) :=
  Action.of (groupSpaceOp d) (baseSpace d)

/-- The underlying object of `action d` is `baseSpace d`. -/
theorem action_X (d : ℕ) [NeZero d] : (action d).X = baseSpace d :=
  rfl

/-- On scheme-valued points, the opposite-group action is identified with conjugation. -/
theorem action_apply {d : ℕ} [NeZero d] {E : AlgebraicSpace specZ}
    (g : E ⟶ space d) (x : E ⟶ baseSpaceLeft d) (T : (Over specZ)ᵒᵖ)
    (p : E.functorOfPoints.obj T) :
    schemeHomEquiv T.unop.left d ((spaceAction g x).app T p).left =
      FreeDimAlgebra.conjugate (homEquiv d T.unop (g.app T p))
        (schemeHomEquiv T.unop.left d (x.app T p).left) :=
  sorry

/-- The action groupoid of `Gᵐᵒᵖ` on `X` in algebraic spaces. -/
def actionGroupoidSpace (d : ℕ) [NeZero d] : GroupoidAlgebraicSpace base :=
  ofAction (groupSpaceOp d) (action d)

/-- The object space of the action groupoid is `baseSpace d`. -/
theorem actionGroupoidSpace_U (d : ℕ) [NeZero d] :
    (actionGroupoidSpace d).U = baseSpace d :=
  rfl

/-- The arrow space of the action groupoid is `Gᵐᵒᵖ ×_base X`. -/
theorem actionGroupoidSpace_R (d : ℕ) [NeZero d] :
    (actionGroupoidSpace d).R = (groupSpaceOp d).X ⊗ baseSpace d :=
  rfl

/-- The source map of the action groupoid is projection onto `X`. -/
theorem actionGroupoidSpace_s (d : ℕ) [NeZero d] :
    (actionGroupoidSpace d).s = actionSource (groupSpaceOp d) (action d) :=
  rfl

/-- The target map of the action groupoid is the conjugation action. -/
theorem actionGroupoidSpace_t (d : ℕ) [NeZero d] :
    (actionGroupoidSpace d).t = actionTarget (groupSpaceOp d) (action d) :=
  rfl

/-- The source and target maps of the action groupoid are smooth. -/
theorem instSmooth_ofAction (d : ℕ) [NeZero d] :
    GroupoidAlgebraicSpace.Smooth (actionGroupoidSpace d) :=
  sorry

/-- The quotient stack `[X/G]` of the opposite-group conjugation action, as the
stackification of the action-groupoid prestack. -/
abbrev quotient (d : ℕ) [NeZero d] : GroupoidsOver specZ :=
  SmallQuotient.quotientStack (actionGroupoidSpace d)

/-- `quotient d` is the quotient stack of the action groupoid of `Gᵐᵒᵖ` on `X`. -/
theorem quotient_eq (d : ℕ) [NeZero d] :
    quotient d = SmallQuotient.quotientStack (ofAction (groupSpaceOp d) (action d)) :=
  rfl

/-- The stackification comparison `[X/_p G] ⟶ [X/G]`. -/
def stackificationHom (d : ℕ) [NeZero d] :
    SmallQuotient.preQuotient (actionGroupoidSpace d) ⟶ quotient d :=
  SmallQuotient.stackificationHom (actionGroupoidSpace d)

/-- `stackificationHom d` is a stackification of the action-groupoid prestack. -/
theorem stackificationHom_isStackification (d : ℕ) [NeZero d] :
    FiberedCategoryOver.Groupoids.Hom.IsStackification
      (Scheme.fppfTopology.over specZ) (stackificationHom d) :=
  SmallQuotient.stackificationHom_isStackification (actionGroupoidSpace d)

/-- The quotient stack `[X/G]` is an algebraic stack, since the action groupoid is smooth. -/
instance instAlgebraicStack_quotient (d : ℕ) [NeZero d] :
    AlgebraicStack (quotient d) :=
  @instAlgebraicStack_quotientStack specZ base (actionGroupoidSpace d) (instSmooth_ofAction d)

end AlgebraicGeometry.GLFixOne
