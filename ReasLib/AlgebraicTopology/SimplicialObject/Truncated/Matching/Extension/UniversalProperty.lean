module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Representability
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
@stack 0188

# Universal property of one-step matching extensions

A one-step extension packages a right Kan extension whose transported top faces and degeneracies
are the universal maps selected by a representation of matching face families.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SimplexCategory.Truncated
open scoped Simplicial SimplexCategory.Truncated

universe v u

namespace CategoryTheory.SimplicialObject.Truncated.matching

variable {C : Type u} [Category.{v} C]

/-- A one-step extension realizing a chosen representation of the next matching-family
functor. The structure records a right Kan extension with the prescribed old and top terms;
its laws identify the actual face and degeneracy maps with the represented universal maps. -/
@[stacks 0188 "one-step matching extension"]
structure Extension {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    (R : (FaceFamily.presheaf U).RepresentableBy T) where
  /-- The truncated simplicial object obtained by adding degree `n + 1`. -/
  obj : SimplicialObject.Truncated C (n + 1)
  /-- The old part of the extension is canonically the original truncated simplicial object. -/
  truncIso : (Truncated.trunc C (n + 1) n).obj obj ≅ U
  /-- The new top-degree term is the chosen representing object. -/
  topIso : obj.obj (op ⦋n + 1⦌ₙ₊₁) ≅ T
  /-- The extension object is a right Kan extension along one-step truncation. -/
  [isRightKanExtension : obj.IsRightKanExtension truncIso.hom]
  /-- After transporting along the comparison isomorphisms, each face is the corresponding
  coordinate of the universal matching family. -/
  face_eq_π (i : Fin (n + 2)) :
    topIso.inv ≫ obj.δ i ≫
        truncIso.hom.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) =
      FaceFamily.π R i
  /-- After transporting along the comparison isomorphisms, each degeneracy is the morphism
  represented by its canonical matching family. -/
  degeneracy_eq_σ (j : Fin (n + 1)) :
    truncIso.inv.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) ≫
          obj.σ j ≫ topIso.hom =
      FaceFamily.σ R j

attribute [stacks 0187 "right Kan universal property of a one-step extension"]
  Extension.isRightKanExtension
attribute [instance] Extension.isRightKanExtension
attribute [stacks 0188 "one-step extension object"] Extension.obj
attribute [stacks 0188 "one-step extension truncation comparison"] Extension.truncIso
attribute [stacks 0188 "one-step extension top-degree comparison"] Extension.topIso
attribute [stacks 0188 "one-step extension face identification"] Extension.face_eq_π
attribute [stacks 0188 "one-step extension degeneracy identification"]
  Extension.degeneracy_eq_σ

namespace Extension

/-- Transport a one-step extension along a change of representing object. The successor-truncated
object and its old-degree comparison are unchanged; only the top-degree comparison is transported
through uniqueness of representing objects. -/
@[stacks 0187 "change of matching representation"]
noncomputable def changeRepresentation {n : ℕ}
    {U : SimplicialObject.Truncated C n} {T T' : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E : Extension R)
    (R' : (FaceFamily.presheaf U).RepresentableBy T') : Extension R' where
  obj := E.obj
  truncIso := E.truncIso
  topIso := E.topIso ≪≫ R.uniqueUpToIso R'
  isRightKanExtension := E.isRightKanExtension
  face_eq_π := sorry
  degeneracy_eq_σ := sorry

/-- The universal Hom equivalence of a one-step matching extension. -/
@[stacks 0187 "one-step extension Hom equivalence"]
noncomputable def homEquiv {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E : Extension R)
    {V : SimplicialObject.Truncated C (n + 1)} :
    (V ⟶ E.obj) ≃
      ((Truncated.trunc C (n + 1) n).obj V ⟶ U) :=
  E.obj.homEquivOfIsRightKanExtension E.truncIso.hom V

/-- The Hom equivalence of an extension sends a morphism to its truncation followed by the
comparison with the original truncated object. -/
@[simp, stacks 0187 "one-step extension Hom equivalence formula"]
theorem homEquiv.apply {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E : Extension R)
    {V : SimplicialObject.Truncated C (n + 1)} (g : V ⟶ E.obj) :
    E.homEquiv g =
      (Truncated.trunc C (n + 1) n).map g ≫ E.truncIso.hom := sorry

/-- The inverse extension Hom equivalence restricts a morphism back to its prescribed truncated
map. -/
@[simp, stacks 0187 "one-step extension inverse Hom equivalence restriction"]
theorem homEquiv.symm_apply {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E : Extension R)
    {V : SimplicialObject.Truncated C (n + 1)}
    (f : (Truncated.trunc C (n + 1) n).obj V ⟶ U) :
    (Truncated.trunc C (n + 1) n).map ((E.homEquiv (V := V)).symm f) ≫ E.truncIso.hom = f := sorry

/-- The extension Hom equivalence respects precomposition. -/
@[stacks 0187 "one-step extension Hom equivalence precomposition"]
theorem homEquiv.comp {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E : Extension R)
    {V W : SimplicialObject.Truncated C (n + 1)} (f : V ⟶ W) (g : W ⟶ E.obj) :
    E.homEquiv (f ≫ g) =
      (Truncated.trunc C (n + 1) n).map f ≫ E.homEquiv g := sorry

/-- The represented-presheaf presentation induced by the right Kan universal property of an
extension. -/
@[stacks 0187 "represented restriction of a one-step extension"]
noncomputable def representableBy {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E : Extension R) :
    ((Truncated.trunc C (n + 1) n).op ⋙ yoneda.obj U).RepresentableBy E.obj where
  homEquiv := E.homEquiv
  homEquiv_comp f g := homEquiv.comp E f g

/-- The truncation comparison of an extension is a universal element for its represented
restriction presheaf. -/
@[stacks 0187 "universal restriction element of a one-step extension"]
theorem isRepresentedBy {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E : Extension R) :
    ((Truncated.trunc C (n + 1) n).op ⋙ yoneda.obj U).IsRepresentedBy
      E.truncIso.hom := sorry

/-- The canonical isomorphism between two one-step extensions realizing the same represented
matching object. -/
@[stacks 0187 "uniqueness of one-step matching extensions"]
noncomputable def uniqueIso {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E E' : Extension R) :
    E.obj ≅ E'.obj :=
  E.obj.rightKanExtensionUnique E.truncIso.hom E'.obj E'.truncIso.hom

/-- The uniqueness isomorphism from an extension to itself is the identity. -/
@[simp, stacks 0187 "self-coherence of extension uniqueness"]
theorem uniqueIso.self {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E : Extension R) :
    E.uniqueIso E = Iso.refl E.obj := sorry

/-- The uniqueness isomorphism is symmetric after taking the inverse isomorphism. -/
@[stacks 0187 "symmetry of extension uniqueness"]
theorem uniqueIso.symm {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E E' : Extension R) :
    (E.uniqueIso E').symm = E'.uniqueIso E := sorry

/-- Uniqueness isomorphisms compose coherently across three matching extensions. -/
@[stacks 0187 "transitivity of extension uniqueness"]
theorem uniqueIso.trans {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T}
    (E E' E'' : Extension R) :
    E.uniqueIso E' ≪≫ E'.uniqueIso E'' = E.uniqueIso E'' := sorry

/-- The canonical isomorphism between extensions commutes with their restriction comparisons. -/
@[reassoc (attr := simp), stacks 0187 "uniqueness isomorphism restriction compatibility"]
theorem uniqueIso.hom_trunc {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E E' : Extension R) :
    (Truncated.trunc C (n + 1) n).map (E.uniqueIso E').hom ≫ E'.truncIso.hom =
      E.truncIso.hom := sorry

/-- The top component of the canonical isomorphism between extensions respects their chosen
identifications with the representing object. -/
@[reassoc (attr := simp), stacks 0187 "uniqueness isomorphism top compatibility"]
theorem uniqueIso.hom_top {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E E' : Extension R) :
    (E.uniqueIso E').hom.app (op ⦋n + 1⦌ₙ₊₁) ≫ E'.topIso.hom =
      E.topIso.hom := sorry

/-- The inverse canonical isomorphism between extensions commutes with their restriction
comparisons. -/
@[reassoc (attr := simp), stacks 0187 "inverse uniqueness isomorphism restriction compatibility"]
theorem uniqueIso.inv_trunc {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E E' : Extension R) :
    (Truncated.trunc C (n + 1) n).map (E.uniqueIso E').inv ≫ E.truncIso.hom =
      E'.truncIso.hom := sorry

/-- The top component of the inverse canonical isomorphism between extensions respects their
chosen identifications with the representing object. -/
@[reassoc (attr := simp), stacks 0187 "inverse uniqueness isomorphism top compatibility"]
theorem uniqueIso.inv_top {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E E' : Extension R) :
    (E.uniqueIso E').inv.app (op ⦋n + 1⦌ₙ₊₁) ≫ E.topIso.hom =
      E'.topIso.hom := sorry

/-- The `i`-th face of a one-step matching extension, transported to the chosen representing
object and the original top-degree term. -/
@[stacks 0188 "one-step extension face"]
def face {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E : Extension R)
    (i : Fin (n + 2)) : T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) :=
  E.topIso.inv ≫ E.obj.δ i ≫
    E.truncIso.hom.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n))

/-- The `j`-th degeneracy of a one-step matching extension, transported from the original
top-degree term to the chosen representing object. -/
@[stacks 0188 "one-step extension degeneracy"]
def degeneracy {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E : Extension R)
    (j : Fin (n + 1)) : U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) ⟶ T :=
  E.truncIso.inv.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) ≫
    E.obj.σ j ≫ E.topIso.hom

/-- A transported extension face is the corresponding represented universal face. -/
@[simp, stacks 0188 "one-step extension universal face"]
theorem face.eq_π {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E : Extension R)
    (i : Fin (n + 2)) :
    E.face i = FaceFamily.π R i := sorry

/-- A transported extension degeneracy is the corresponding represented universal
degeneracy. -/
@[simp, stacks 0188 "one-step extension universal degeneracy"]
theorem degeneracy.eq_σ {n : ℕ} {U : SimplicialObject.Truncated C n} {T : C}
    {R : (FaceFamily.presheaf U).RepresentableBy T} (E : Extension R)
    (j : Fin (n + 1)) :
    E.degeneracy j = FaceFamily.σ R j := sorry

end Extension

end CategoryTheory.SimplicialObject.Truncated.matching
