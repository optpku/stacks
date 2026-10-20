module

public import ReasLib.AlgebraicGeometry.RingedSite.DifferentialGraded.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import stacks_project.Chap92.«92_4_0_1_Morphism»
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver
public import stacks_project.Chap92.«92_7_0_2_Triple»

/-!
# Ringed topos maps from the triple polynomial site

The functors `u1`, `u2`, `u3` of opposite polynomial sites induce morphisms of ringed
topoi `g1`, `g2`, `g3` with structure sheaves `O_i = g_i⁻¹ O` obtained by precomposition.
-/

@[expose] public section

open CategoryTheory Opposite
open Algebra
open CommAlgCat.Over.Polynomial
open RingedSite
open RingedSite.Chaotic
open scoped TensorProduct

noncomputable section

universe u

namespace RingedSite.Cotangent.PolynomialTriple

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- The opposite functor `u1 : C_{C/B/A} ⥤ C_{B/A}`, sending `(P ⟶ B, Q ⟶ C)` to `(P ⟶ B)`. -/
def u1 : (PolynomialTriple A B C)ᵒᵖ ⥤ PolynomialSite A B :=
  (forgetToBase A B C).op

/-- The opposite functor `u2 : C_{C/B/A} ⥤ C_{C/A}`, sending `(P ⟶ B, Q ⟶ C)` to `(Q ⟶ C)`. -/
def u2 : (PolynomialTriple A B C)ᵒᵖ ⥤ PolynomialSite A C :=
  (forgetToOverA A B C).op

/-- The opposite functor `u3 : C_{C/B/A} ⥤ C_{C/B}`, sending `(P ⟶ B, Q ⟶ C)` to
`(Q ⊗[P] B ⟶ C)`. -/
def u3 : (PolynomialTriple A B C)ᵒᵖ ⥤ PolynomialSite B C :=
  (forgetToOverB A B C).op

/-- Objects of `u1` are the opposite first-factor polynomial algebras over `B`. -/
theorem u1_obj (X : PolynomialTriple A B C) :
    (u1 A B C).obj (op X) = op (forgetToBaseObj X) := sorry

/-- Objects of `u2` are the opposite second-factor rings `Q` mapping to `C` over `A`. -/
theorem u2_obj (X : PolynomialTriple A B C) :
    (u2 A B C).obj (op X) = op (forgetToOverAObj X) := sorry

/-- Objects of `u3` are the opposite tensors `Q ⊗[P] B` mapping to `C`. -/
theorem u3_obj (X : PolynomialTriple A B C) :
    (u3 A B C).obj (op X) = op (tensorOverBase X) := sorry

/-- Pointwise right Kan extensions of type-valued presheaves along `u1ᵒᵖ`. -/
instance u1_op_hasPointwiseRightKanExtension
    (P : ((PolynomialTriple A B C)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)) :
    (u1 A B C).op.HasPointwiseRightKanExtension P := sorry

/-- Pointwise right Kan extensions of type-valued presheaves along `u2ᵒᵖ`. -/
instance u2_op_hasPointwiseRightKanExtension
    (P : ((PolynomialTriple A B C)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)) :
    (u2 A B C).op.HasPointwiseRightKanExtension P := sorry

/-- Pointwise right Kan extensions of type-valued presheaves along `u3ᵒᵖ`. -/
instance u3_op_hasPointwiseRightKanExtension
    (P : ((PolynomialTriple A B C)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)) :
    (u3 A B C).op.HasPointwiseRightKanExtension P := sorry

/-- The structure sheaf `O1 = u1⁻¹ O` on `C_{C/B/A}`. -/
def structureSheaf1 :
    Sheaf (⊥ : GrothendieckTopology (PolynomialTriple A B C)ᵒᵖ) CommRingCat.{u + 1} :=
  restrictSheaf (u1 A B C) (Site.structureSheafLift A B)

/-- The structure sheaf `O2 = u2⁻¹ O` on `C_{C/B/A}`. -/
def structureSheaf2 :
    Sheaf (⊥ : GrothendieckTopology (PolynomialTriple A B C)ᵒᵖ) CommRingCat.{u + 1} :=
  restrictSheaf (u2 A B C) (Site.structureSheafLift A C)

/-- The structure sheaf `O3 = u3⁻¹ O` on `C_{C/B/A}`. -/
def structureSheaf3 :
    Sheaf (⊥ : GrothendieckTopology (PolynomialTriple A B C)ᵒᵖ) CommRingCat.{u + 1} :=
  restrictSheaf (u3 A B C) (Site.structureSheafLift B C)

/-- The ringed site `(Sh(C_{C/B/A}), O1)`. -/
def ringedSite1 : RingedSite.{u + 1, u, u + 1} :=
  ofCommRingSheaf (⊥ : GrothendieckTopology (PolynomialTriple A B C)ᵒᵖ)
    (structureSheaf1 A B C)

/-- The ringed site `(Sh(C_{C/B/A}), O2)`. -/
def ringedSite2 : RingedSite.{u + 1, u, u + 1} :=
  ofCommRingSheaf (⊥ : GrothendieckTopology (PolynomialTriple A B C)ᵒᵖ)
    (structureSheaf2 A B C)

/-- The ringed site `(Sh(C_{C/B/A}), O3)`. -/
def ringedSite3 : RingedSite.{u + 1, u, u + 1} :=
  ofCommRingSheaf (⊥ : GrothendieckTopology (PolynomialTriple A B C)ᵒᵖ)
    (structureSheaf3 A B C)

/-- `O1` evaluates to the universe lift of the first source ring `P`. -/
theorem structureSheaf1_obj (X : PolynomialTriple A B C) :
    (structureSheaf1 A B C).obj.obj (op (op X)) =
      (Site.uliftCommRing).obj (CommRingCat.of X.P) := sorry

/-- `O2` evaluates to the universe lift of the second source ring `Q`. -/
theorem structureSheaf2_obj (X : PolynomialTriple A B C) :
    (structureSheaf2 A B C).obj.obj (op (op X)) =
      (Site.uliftCommRing).obj (CommRingCat.of X.Q) := sorry

/-- `O3` evaluates to the universe lift of the tensor ring `Q ⊗[P] B`. -/
theorem structureSheaf3_obj (X : PolynomialTriple A B C) :
    (structureSheaf3 A B C).obj.obj (op (op X)) =
      (Site.uliftCommRing).obj
        ((forget₂ (CommAlgCat B) CommRingCat).obj (tensorOverBase X).obj.left) := sorry

/-- A cocontinuous functor of chaotic sites, with its structure-presheaf map, induces a
morphism of ringed topoi. Pointwise right Kan extensions are instance parameters, supplied
by the named `u1`/`u2`/`u3` obligations. -/
def ofCocontinuous {src : Type (u + 1)} [Category.{u} src]
    {tgt : Type (u + 1)} [Category.{u} tgt] (G : src ⥤ tgt)
    [∀ P : srcᵒᵖ ⥤ Type (u + 1), G.op.HasPointwiseRightKanExtension P]
    (OC : Sheaf (⊥ : GrothendieckTopology src) RingCat.{u + 1})
    (OD : Sheaf (⊥ : GrothendieckTopology tgt) RingCat.{u + 1})
    (η : G.op ⋙ OD.obj ⟶ OC.obj) :
    ToposHom (ofRingSheaf ⊥ OC) (ofRingSheaf ⊥ OD) :=
  Cocontinuous.toRingedTopos G η

/-- Identity structure-presheaf map for `g1`. -/
def toBase_η :
    (u1 A B C).op ⋙ (Site.ringedSite A B).structureSheaf.obj ⟶
      (ringedSite1 A B C).structureSheaf.obj :=
  𝟙 _

/-- The morphism of ringed topoi `g1` induced by `u1`. -/
def toBase : ToposHom (ringedSite1 A B C) (Site.ringedSite A B) :=
  ofCocontinuous (u1 A B C) (ringedSite1 A B C).structureSheaf
    (Site.ringedSite A B).structureSheaf (toBase_η A B C)

/-- Identity structure-presheaf map for `g2`. -/
def toOverA_η :
    (u2 A B C).op ⋙ (Site.ringedSite A C).structureSheaf.obj ⟶
      (ringedSite2 A B C).structureSheaf.obj :=
  𝟙 _

/-- The morphism of ringed topoi `g2` induced by `u2`. -/
def toOverA : ToposHom (ringedSite2 A B C) (Site.ringedSite A C) :=
  ofCocontinuous (u2 A B C) (ringedSite2 A B C).structureSheaf
    (Site.ringedSite A C).structureSheaf (toOverA_η A B C)

/-- Identity structure-presheaf map for `g3`. -/
def toOverB_η :
    (u3 A B C).op ⋙ (Site.ringedSite B C).structureSheaf.obj ⟶
      (ringedSite3 A B C).structureSheaf.obj :=
  𝟙 _

/-- The morphism of ringed topoi `g3` induced by `u3`. -/
def toOverB : ToposHom (ringedSite3 A B C) (Site.ringedSite B C) :=
  ofCocontinuous (u3 A B C) (ringedSite3 A B C).structureSheaf
    (Site.ringedSite B C).structureSheaf (toOverB_η A B C)

/-- The structure sheaf `O1` is the inverse image of `O` along `u1`. -/
theorem toBase_inverseImage_structureSheaf :
    structureSheaf1 A B C = restrictSheaf (u1 A B C) (Site.structureSheafLift A B) := sorry

/-- The structure sheaf `O2` is the inverse image of `O` along `u2`. -/
theorem toOverA_inverseImage_structureSheaf :
    structureSheaf2 A B C = restrictSheaf (u2 A B C) (Site.structureSheafLift A C) := sorry

/-- The structure sheaf `O3` is the inverse image of `O` along `u3`. -/
theorem toOverB_inverseImage_structureSheaf :
    structureSheaf3 A B C = restrictSheaf (u3 A B C) (Site.structureSheafLift B C) := sorry

end RingedSite.Cotangent.PolynomialTriple
