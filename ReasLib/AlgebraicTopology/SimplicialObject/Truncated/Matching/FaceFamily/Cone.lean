/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Diagram
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.FaceFamily.Presheaf
public import ReasLib.AlgebraicTopology.SimplexCategory.HomCode

/-!
@stack 0186

# Explicit face families and matching cones

The next matching diagram has two useful presentations.  Its cones are canonical for category
theory, while `FaceFamily` records only the codimension-one coordinates and their pairwise
compatibility.  This file gives the natural equivalence between those presentations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Truncated.matching

variable {C : Type u} [Category.{v} C]

namespace index

/-- The truncated simplex underlying an object of the next matching index. -/
@[stacks 0186 "simplex underlying a matching index"]
abbrev simplex {n : ℕ} (A : matching.index n) : SimplexCategory.Truncated n :=
  A.right.unop

/-- The simplex map to `[n + 1]` underlying an object of the next matching index. -/
@[stacks 0186 "map underlying a matching index"]
abbrev arrow {n : ℕ} (A : matching.index n) :
    (SimplexCategory.Truncated.inclusion n).obj (simplex A) ⟶ ⦋n + 1⦌ :=
  A.hom.unop

/-- The first vertex omitted by the map underlying a matching-index object. The definition is
total; `chosenMissing.spec` records that the fallback cannot occur for this index shape. -/
@[stacks 0186 "missing face of a matching index"]
def chosenMissing {n : ℕ} (A : matching.index n) : Fin (n + 2) :=
  (SimplexCategory.Hom.targetGap? (arrow A)).getD 0

/-- The chosen vertex is not in the image of the map underlying a matching-index object. -/
@[stacks 0186 "missing-face specification"]
theorem chosenMissing.spec {n : ℕ} (A : matching.index n) :
    ∀ x, (arrow A).toOrderHom x ≠ chosenMissing A := sorry

/-- The canonical factorization of a matching-index map through its chosen missing face. -/
@[stacks 0186 "matching-index face factorization"]
def factor {n : ℕ} (A : matching.index n) :
    simplex A ⟶ (⦋n⦌ₙ : SimplexCategory.Truncated n) :=
  SimplexCategory.Truncated.Hom.tr
    (SimplexCategory.factor_δ (arrow A) (chosenMissing A))
    (simplex A).property le_rfl

/-- The canonical factor followed by its missing coface is the original matching-index map. -/
@[stacks 0186 "matching-index face factorization specification"]
theorem factor.spec {n : ℕ} (A : matching.index n) :
    (factor A).hom ≫ SimplexCategory.δ (chosenMissing A) = arrow A := sorry

end index

namespace FaceFamily

variable {n : ℕ} {U : SimplicialObject.Truncated C n}

namespace Compatible

/-- The codimension-one components of a matching cone satisfy the explicit face-family
compatibility relations. -/
@[stacks 0186 "matching cone face compatibility"]
theorem ofCone {T : C} (s : (matching.diagram U).cones.obj (op T)) :
    FaceFamily.Compatible U (fun i ↦ s.app (matching.face i)) := sorry

end Compatible

/-- Restriction of a full matching cone to its codimension-one face coordinates. -/
@[stacks 0186 "matching cone to explicit face family"]
def ofCone {T : C} (s : (matching.diagram U).cones.obj (op T)) : FaceFamily U T where
  app i := s.app (matching.face i)
  compatible := Compatible.ofCone s

/-- Restricting a matching cone to faces evaluates at the corresponding coface object. -/
@[simp, stacks 0186 "matching cone face coordinate"]
theorem ofCone.app {T : C} (s : (matching.diagram U).cones.obj (op T))
    (i : Fin (n + 2)) :
    (ofCone s).app i = s.app (matching.face i) := sorry

/-- The component at a matching index of the cone reconstructed from a compatible face family. -/
@[stacks 0186 "explicit face-family cone component data"]
def toConeApp {T : C} (F : FaceFamily U T) (A : matching.index n) :
    T ⟶ (matching.diagram U).obj A :=
  F.app (index.chosenMissing A) ≫ U.map (index.factor A).op

/-- The reconstructed component family is natural in the matching index. -/
@[stacks 0186 "explicit face-family cone-component naturality"]
theorem toConeApp.naturality {T : C} (F : FaceFamily U T)
    {A B : matching.index n} (f : A ⟶ B) :
    ((Functor.const (matching.index n)).obj T).map f ≫ toConeApp F B =
      toConeApp F A ≫ (matching.diagram U).map f := sorry

/-- Extension of a compatible face family to the full matching cone.  At an arbitrary index it
uses the chosen missing face and the canonical factor through that face. -/
@[stacks 0186 "explicit face family to matching cone"]
def toCone {T : C} (F : FaceFamily U T) : (matching.diagram U).cones.obj (op T) where
  app := toConeApp F
  naturality := fun {A B} f ↦ toConeApp.naturality F (A := A) (B := B) f

/-- The extended cone is independent of the chosen missing-face presentation: any factorization
of the index map through `δ_i` computes the same component. -/
@[stacks 0186 "explicit face-family cone component"]
theorem toCone.app_of_factorization {T : C} (F : FaceFamily U T) {A : matching.index n}
    (i : Fin (n + 2))
    (ψ : index.simplex A ⟶ (⦋n⦌ₙ : SimplexCategory.Truncated n))
    (hψ : ψ.hom ≫ SimplexCategory.δ i = index.arrow A) :
    F.toCone.app A = F.app i ≫ U.map ψ.op := sorry

/-- Extending a face family and evaluating at a coface recovers that face coordinate. -/
@[simp, stacks 0186 "explicit face-family cone face component"]
theorem toCone.face {T : C} (F : FaceFamily U T) (i : Fin (n + 2)) :
    F.toCone.app (matching.face i) = F.app i := sorry

/-- Restricting a full matching cone after extending it from its face coordinates is the
identity. -/
@[simp, stacks 0186 "matching cone reconstruction from faces"]
theorem coneEquiv.left_inv {T : C} (s : (matching.diagram U).cones.obj (op T)) :
    (ofCone s).toCone = s := sorry

/-- Extending and then restricting a compatible face family is the identity. -/
@[simp, stacks 0186 "explicit face-family reconstruction"]
theorem coneEquiv.right_inv {T : C} (F : FaceFamily U T) :
    ofCone F.toCone = F := sorry

/-- Full matching cones are naturally equivalent to explicit compatible face families. -/
@[stacks 0186 "matching cones equivalent to explicit face families"]
def coneEquiv (U : SimplicialObject.Truncated C n) (T : C) :
    (matching.diagram U).cones.obj (op T) ≃ FaceFamily U T where
  toFun := ofCone
  invFun := toCone
  left_inv := coneEquiv.left_inv
  right_inv := coneEquiv.right_inv

namespace coneEquiv

/-- The forward matching cone equivalence restricts to codimension-one faces. -/
@[simp, stacks 0186 "matching cone equivalence forward formula"]
theorem apply {U : SimplicialObject.Truncated C n} {T : C}
    (s : (matching.diagram U).cones.obj (op T)) :
    coneEquiv U T s = ofCone s := sorry

/-- The inverse matching cone equivalence extends a compatible family to a full cone. -/
@[simp, stacks 0186 "matching cone equivalence inverse formula"]
theorem symm_apply {U : SimplicialObject.Truncated C n} {T : C} (F : FaceFamily U T) :
    (coneEquiv U T).symm F = F.toCone := sorry

/-- The matching-cone equivalences are natural under precomposition of their cone points. -/
@[stacks 0186 "matching cone equivalence naturality"]
theorem naturality {U : SimplicialObject.Truncated C n}
    {T T' : Cᵒᵖ} (f : T ⟶ T') :
    (matching.diagram U).cones.map f ≫ (coneEquiv U T'.unop).toIso.hom =
      (coneEquiv U T.unop).toIso.hom ≫ (FaceFamily.presheaf U).map f := sorry

end coneEquiv

/-- The cone presheaf of the matching diagram is naturally isomorphic to the explicit
face-family presheaf. -/
@[stacks 0186 "matching cone and face-family presheaf comparison"]
def coneIso (U : SimplicialObject.Truncated C n) :
    (matching.diagram U).cones ≅ FaceFamily.presheaf U :=
  NatIso.ofComponents (fun T ↦ (coneEquiv U T.unop).toIso) coneEquiv.naturality

namespace coneIso

/-- The forward map of the cone/face-family presheaf isomorphism restricts a cone to its
codimension-one face coordinates. -/
@[simp, stacks 0186 "matching cone comparison forward formula"]
theorem hom_app {U : SimplicialObject.Truncated C n} {T : C}
    (s : (matching.diagram U).cones.obj (op T)) :
    (FaceFamily.coneIso U).hom.app (op T) s = FaceFamily.ofCone s := sorry

/-- The inverse map of the cone/face-family presheaf isomorphism extends a compatible face
family to the full matching cone. -/
@[simp, stacks 0186 "matching cone comparison inverse formula"]
theorem inv_app {U : SimplicialObject.Truncated C n} {T : C} (F : FaceFamily U T) :
    (FaceFamily.coneIso U).inv.app (op T) F = F.toCone := sorry

end coneIso

/-- A representation of explicit compatible face families also represents the canonical cone
presheaf of the matching diagram. -/
@[stacks 0186 "matching cone representation from face families"]
def coneRepresentableBy {U : SimplicialObject.Truncated C n} {T : C}
    (R : (FaceFamily.presheaf U).RepresentableBy T) :
    (matching.diagram U).cones.RepresentableBy T :=
  R.ofIso (coneIso U).symm

namespace coneRepresentableBy

/-- The cone represented by a morphism is obtained by extending its represented face family. -/
@[simp, stacks 0186 "represented matching cone formula"]
theorem homEquiv_apply {U : SimplicialObject.Truncated C n} {T X : C}
    (R : (FaceFamily.presheaf U).RepresentableBy T) (f : X ⟶ T) :
    (FaceFamily.coneRepresentableBy R).homEquiv f = (R.homEquiv f).toCone := sorry

/-- The inverse represented-cone Hom equivalence restricts a cone to its compatible face family.
-/
@[simp, stacks 0186 "inverse represented matching cone formula"]
theorem homEquiv_symm_apply {U : SimplicialObject.Truncated C n} {T X : C}
    (R : (FaceFamily.presheaf U).RepresentableBy T)
    (s : (matching.diagram U).cones.obj (op X)) :
    (FaceFamily.coneRepresentableBy R).homEquiv.symm s =
      R.homEquiv.symm (FaceFamily.ofCone s) := sorry

end coneRepresentableBy

/-- The matching cone with point `T` determined by a representation of explicit face families. -/
@[stacks 0186 "limit cone from represented face families"]
def limitCone {U : SimplicialObject.Truncated C n} {T : C}
    (R : (FaceFamily.presheaf U).RepresentableBy T) :
    Cone (matching.diagram U) :=
  IsLimit.OfNatIso.limitCone (coneRepresentableBy R)

namespace limitCone

/-- The component of the represented limit cone is obtained by extending the universal face
family to the full matching diagram. -/
@[stacks 0186 "represented matching limit component"]
theorem projection_app {U : SimplicialObject.Truncated C n} {T : C}
    (R : (FaceFamily.presheaf U).RepresentableBy T)
    (A : matching.index n) :
    (FaceFamily.limitCone R).π.app A =
      (R.homEquiv (𝟙 T)).toCone.app A := sorry

/-- On a codimension-one face, the represented limit cone is the corresponding coordinate of
the universal face family. -/
@[simp, stacks 0186 "represented matching limit face component"]
theorem projection_face {U : SimplicialObject.Truncated C n} {T : C}
    (R : (FaceFamily.presheaf U).RepresentableBy T)
    (i : Fin (n + 2)) :
    (FaceFamily.limitCone R).π.app (matching.face i) =
      (R.homEquiv (𝟙 T)).app i := sorry

/-- The cone determined by a representation of the explicit compatible face-family presheaf is
a limit cone. -/
@[stacks 0186]
def isLimit {U : SimplicialObject.Truncated C n} {T : C}
    (R : (FaceFamily.presheaf U).RepresentableBy T) :
    IsLimit (FaceFamily.limitCone R) :=
  IsLimit.ofRepresentableBy (coneRepresentableBy R)

end limitCone

end FaceFamily

end CategoryTheory.SimplicialObject.Truncated.matching
