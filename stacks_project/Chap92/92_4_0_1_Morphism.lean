/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import ReasLib.CategoryTheory.ObjectProperty.Over.Basic
public import ReasLib.CategoryTheory.Sites.Chaotic
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver
public import stacks_project.Chap92.«92_4_0_1_Polynomial»

/-!
# The polynomial site `C_{B/A}` and the morphisms `i`, `π`

This leaf owns the opposite chaotic site of polynomial `A`-algebras over `B`, the structure
sheaf `O`, the constant sheaf `underline{B}`, and the morphisms of ringed topoi
`i : (Sh(C), underline{B}) ⟶ (Sh(C), O)` and `π : (Sh(C), underline{B}) ⟶ (Sh(*), B)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open RingedSite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace CommAlgCat.Over.Polynomial

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The site `C_{B/A}` is the opposite of the category of polynomial `A`-algebras over `B`. -/
abbrev site := Algebra.PolynomialSite A B

/-- Objects of `site A B` are polynomial `A`-algebra maps to `B`. -/
theorem site_unop_mem (X : site A B) : property A B X.unop.obj :=
  sorry

namespace Site

/-- Universe lift of commutative rings, used to present ringed topoi on the large site
`C_{B/A}` with coefficient universe `u + 1`. -/
def uliftCommRing : CommRingCat.{u} ⥤ CommRingCat.{u + 1} where
  obj R := CommRingCat.of (ULift.{u + 1} R)
  map f :=
    CommRingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp (f.hom.comp ULift.ringEquiv.toRingHom))

/-- The chaotic Grothendieck topology on `C_{B/A}`. -/
abbrev topology : GrothendieckTopology (site A B) := ⊥

/-- The chaotic topology on `C_{B/A}` is the bottom Grothendieck topology. -/
theorem topology_eq_bot : topology A B = ⊥ := sorry

/-- The chaotic topology on `C_{B/A}` is `GrothendieckTopology.trivial`. -/
theorem topology_eq_trivial :
    topology A B = GrothendieckTopology.trivial (site A B) := sorry

/-- The underlying presheaf of `O`, sending `(P, α)` to the source ring `P`. -/
def structurePresheaf : (site A B)ᵒᵖ ⥤ CommRingCat.{u} :=
  unopUnop (Algebra.PolynomialOver A B) ⋙
    ObjectProperty.Over.forgetDiagram (Algebra.isPolynomialOver A B) ⋙
      forget₂ (CommAlgCat A) CommRingCat

/-- The structure sheaf `O` on `C_{B/A}`, sending `(P, α)` to `P`. -/
def structureSheaf : Sheaf (topology A B) CommRingCat.{u} :=
  ⟨structurePresheaf A B, Presheaf.isSheaf_bot _⟩

/-- The constant sheaf `underline{B}` on `C_{B/A}`. -/
def constantRingSheaf : Sheaf (topology A B) CommRingCat.{u} :=
  ⟨(Functor.const _).obj (CommRingCat.of B), Presheaf.isSheaf_bot _⟩

/-- The sheaf morphism `i♯ : O ⟶ underline{B}` whose component at `(P, α)` is the
augmentation `α : P → B`. -/
def structureSheafMap : structureSheaf A B ⟶ constantRingSheaf A B :=
  ObjectProperty.homMk
    { app := fun X ↦
        (forget₂ (CommAlgCat A) CommRingCat).map
          ((ObjectProperty.Over.forgetCocone (Algebra.isPolynomialOver A B)).ι.app
            ((unopUnop (Algebra.PolynomialOver A B)).obj X))
      naturality := fun _ _ _ ↦ sorry }

/-- `O`, lifted to `CommRingCat.{u + 1}` for the ringed-topos presentation. -/
def structureSheafLift : Sheaf (topology A B) CommRingCat.{u + 1} :=
  (sheafCompose (topology A B) (uliftCommRing)).obj (structureSheaf A B)

/-- `underline{B}`, lifted to `CommRingCat.{u + 1}` for the ringed-topos presentation. -/
def constantRingSheafLift : Sheaf (topology A B) CommRingCat.{u + 1} :=
  (sheafCompose (topology A B) (uliftCommRing)).obj (constantRingSheaf A B)

/-- The lifted structure map `i♯`. -/
def structureSheafMapLift : structureSheafLift A B ⟶ constantRingSheafLift A B :=
  (sheafCompose (topology A B) (uliftCommRing)).map (structureSheafMap A B)

/-- The ringed site `(Sh(C), O)`. -/
def ringedSite : RingedSite.{u + 1, u, u + 1} :=
  ofCommRingSheaf (topology A B) (structureSheafLift A B)

/-- The ringed site `(Sh(C), underline{B})`. -/
def constantRingedSite : RingedSite.{u + 1, u, u + 1} :=
  ofCommRingSheaf (topology A B) (constantRingSheafLift A B)

/-- The point category `*` as `Discrete PUnit`. -/
abbrev pointSite : Type (u + 1) := Discrete PUnit.{u + 2}

/-- The chaotic topology on the point category. -/
abbrev pointTopology : GrothendieckTopology (pointSite) := ⊥

/-- The constant sheaf of rings `B` on the point. -/
def pointRingSheaf : Sheaf (pointTopology) CommRingCat.{u + 1} :=
  ⟨(Functor.const _).obj (CommRingCat.of (ULift.{u + 1} B)), Presheaf.isSheaf_bot _⟩

/-- The ringed site `(Sh(*), B)`. -/
def pointRingedSite : RingedSite.{u + 1, u + 1, u + 1} :=
  ofCommRingSheaf pointTopology (pointRingSheaf B)

/-- Evaluation of `O` at a polynomial object recovers the underlying source ring. -/
theorem structureSheaf_obj (X : (site A B)ᵒᵖ) :
    (structureSheaf A B).obj.obj X =
      (forget₂ (CommAlgCat A) CommRingCat).obj
        ((unopUnop (Algebra.PolynomialOver A B)).obj X).obj.left := sorry

/-- Evaluation of `underline{B}` is constantly `B`. -/
theorem constantRingSheaf_obj (X : (site A B)ᵒᵖ) :
    (constantRingSheaf A B).obj.obj X = CommRingCat.of B := sorry

/-- Components of `i♯` are the Over-structure morphisms `α : P → B`. -/
theorem structureSheafMap_app (X : (site A B)ᵒᵖ) :
    (structureSheafMap A B).hom.app X =
      (forget₂ (CommAlgCat A) CommRingCat).map
        ((unopUnop (Algebra.PolynomialOver A B)).obj X).obj.hom := sorry

/-- The same-site morphism of ringed sites with identity base functor and structure map `i♯`. -/
def sameSite : constantRingedSite A B ⟶ ringedSite A B :=
  sameSiteHom.{u + 1, u, u + 1} (structureSheafMapLift A B)

/-- The morphism of ringed topoi `i : (Sh(C), underline{B}) ⟶ (Sh(C), O)`, identity on
underlying topoi, with `i♯ : O ⟶ underline{B}` the augmentations. -/
def i : ToposHom (constantRingedSite A B) (ringedSite A B) :=
  Hom.toToposHom (sameSite A B)

/-- The category-to-point functor `C_{B/A} ⥤ *`. -/
def toPointBase : constantRingedSite A B ⥤ pointRingedSite B :=
  Functor.star.{u + 1, u, u + 1} (site A B)

/-- Every functor of chaotic sites is cocontinuous; in particular the category-to-point functor
is cocontinuous. -/
instance toPointBase_isCocontinuous :
    (toPointBase A B).IsCocontinuous
      (constantRingedSite A B).siteTopology (pointRingedSite B).siteTopology :=
  Functor.isCocontinuous_bot (toPointBase A B)

/-- The constant-to-constant comparison identifying the pullback of `B` along `star`
with `underline{B}`. -/
def toPointStructureMap :
    (toPointBase A B).op ⋙ (pointRingedSite B).structureSheaf.obj ⟶
      (constantRingedSite A B).structureSheaf.obj :=
  𝟙 _

/-- The morphism of ringed topoi `π : (Sh(C), underline{B}) ⟶ (Sh(*), B)`. -/
def toPoint : ToposHom (constantRingedSite A B) (pointRingedSite B) :=
  Cocontinuous.toRingedTopos (toPointBase A B) (toPointStructureMap A B)

/-- The underlying functor of `π` is `Functor.star`. -/
theorem toPoint_star :
    toPointBase A B = Functor.star.{u + 1, u, u + 1} (site A B) := sorry

/-- Inverse image of the constant sheaf `B` along `π` recovers `underline{B}`. -/
theorem toPoint_inverseImage_constant :
    (toPointBase A B).op ⋙ (pointRingedSite B).structureSheaf.obj =
      (constantRingedSite A B).structureSheaf.obj := sorry

/-- The universe lift sends a commutative ring `R` to `ULift R`. -/
theorem uliftCommRing_obj (R : CommRingCat.{u}) :
    (uliftCommRing).obj R = CommRingCat.of (ULift.{u + 1} R) := sorry

/-- The base functor of `i` is the identity of `C_{B/A}`. -/
theorem i_base : (sameSite A B).base = 𝟭 (site A B) := sorry

end Site

end CommAlgCat.Over.Polynomial
