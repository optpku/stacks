module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap68.Lemma_68_18_6_Fibre
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.LocallyNoetherian

/-!
# Fibres of morphisms of algebraic spaces over field-valued points

The fibre of a morphism `f : X ⟶ Y` of algebraic spaces over a field-valued
point `p` of `Y` is the fibre product `fieldFiber f p = pullback f p.hom`.
Residue-field fibres along étale scheme charts are the special case of the
canonical residue-field point of the chart, mapped to `Y`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The projection of the fibre over a field-valued point to the source. -/
def fiberι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) : fieldFiber f p ⟶ X :=
  fieldFiberι f p

#check (AlgebraicGeometry.AlgebraicSpace.fieldFiberι_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y), fieldFiberι f p = pullback.fst f p.hom)

/-- The structure morphism of the fibre over a field-valued point to `Spec(p.K)`. -/
def fiberToSpec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) : fieldFiber f p ⟶ ofOver p.overObj :=
  fieldFiberToSpec f p

#check (AlgebraicGeometry.AlgebraicSpace.fieldFiberToSpec_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y), fieldFiberToSpec f p = pullback.snd f p.hom)

/-- The fibre square of `f` over a field-valued point is a pullback square. -/
theorem isPullback_fiberOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) :
    IsPullback (fiberι f p) (fiberToSpec f p) f p.hom :=
  fieldFiber_isPullback f p

end AlgebraicGeometry.AlgebraicSpace
