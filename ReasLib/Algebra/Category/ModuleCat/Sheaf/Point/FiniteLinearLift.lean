module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.Finite.Sum

/-!
# Lifting finite module maps from a stalk

A linear map from a finite module over a finite ring into a stalk can be represented by a
linear map into sections on one pointed neighborhood. The construction first lifts its
finitely many values, then refines the neighborhood so that the finitely many linearity
equations hold simultaneously.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u r m i

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C] (Φ : Point.{w} J)
variable {R : Type r} [Ring R]
variable [HasColimitsOfSize.{w, w} (ModuleCat.{m} R)]
variable [PreservesFilteredColimitsOfSize.{w, w} (forget (ModuleCat.{m} R))]
variable (P : Cᵒᵖ ⥤ ModuleCat.{m} R)

/-- A finite family of stalk values represented on one pointed neighborhood. -/
structure FiniteRepresentative {ι : Type i} (s : ι → (Φ.presheafFiber (A := ModuleCat.{m} R)).obj P) where
  U : C
  point : Φ.fiber.obj U
  values : ι → P.obj (op U)
  germ_eq (j : ι) : Φ.toPresheafFiber U point P (values j) = s j

/-- Represent each value and restrict all of them to a genuine common refinement. -/
def finiteRepresentative {ι : Type i} [Finite ι] (s : ι → (Φ.presheafFiber (A := ModuleCat.{m} R)).obj P) :
    FiniteRepresentative Φ P s := by
  classical
  letI := Fintype.ofFinite ι
  let h j := Φ.toPresheafFiber_jointly_surjective (P := P) (s j)
  let N (j : ι) : Φ.fiber.Elements := ⟨(h j).choose, (h j).choose_spec.choose⟩
  let hs := IsCofiltered.inf_objs_exists (Finset.univ.image N)
  let T := hs.choose
  let f (j : ι) : T ⟶ N j := (hs.choose_spec (Finset.mem_image_of_mem N (Finset.mem_univ j))).some
  exact
    { U := T.1
      point := T.2
      values := fun j ↦ P.map (f j).val.op (h j).choose_spec.choose_spec.choose
      germ_eq := fun j ↦ by
        have e := ConcreteCategory.congr_hom
          (Φ.toPresheafFiber_w (f j).val T.2 P) (h j).choose_spec.choose_spec.choose
        rw [(f j).property] at e
        exact e.trans (h j).choose_spec.choose_spec.choose_spec }

/-- A refinement on which two sections with the same germ agree. -/
structure EqualityRefinement (N : Φ.fiber.Elements) (s t : P.obj (op N.1)) where
  neighborhood : Φ.fiber.Elements
  map : neighborhood ⟶ N
  eq_map : P.map map.val.op s = P.map map.val.op t

/-- Equality of germs gives an actual refining neighborhood and equality of restricted sections. -/
def equalityRefinement (N : Φ.fiber.Elements) (s t : P.obj (op N.1))
    (h : Φ.toPresheafFiber N.1 N.2 P s = Φ.toPresheafFiber N.1 N.2 P t) :
    EqualityRefinement Φ P N s t := by
  classical
  let e := (Φ.toPresheafFiber_eq_iff' N.1 N.2 s t).mp h
  exact
    { neighborhood := ⟨e.choose, e.choose_spec.choose_spec.choose⟩
      map := ⟨e.choose_spec.choose, e.choose_spec.choose_spec.choose_spec.1⟩
      eq_map := e.choose_spec.choose_spec.choose_spec.2 }

/-- A linear map into a stalk represented by a linear map on one pointed neighborhood. -/
structure LinearLift (M : ModuleCat.{m} R) (f : M ⟶ (Φ.presheafFiber (A := ModuleCat.{m} R)).obj P) where
  U : C
  point : Φ.fiber.obj U
  map : M ⟶ P.obj (op U)
  map_germ : map ≫ Φ.toPresheafFiber U point P = f

/-- Lift the finitely many values and impose all addition and scalar equations on one
common refinement. All chosen neighborhoods come from native, proved colimit properties. -/
def linearLiftOfFinite [Finite R] (M : ModuleCat.{m} R) [Finite M]
    (f : M ⟶ (Φ.presheafFiber (A := ModuleCat.{m} R)).obj P) : LinearLift Φ P M f := by
  classical
  let t := Φ.finiteRepresentative P (fun x : M ↦ f x)
  let N : Φ.fiber.Elements := ⟨t.U, t.point⟩
  let E := (M × M) ⊕ (R × M)
  letI : Finite E := inferInstanceAs (Finite ((M × M) ⊕ (R × M)))
  let a : E → P.obj (op N.1) := Sum.elim
    (fun x ↦ t.values (x.1 + x.2)) (fun x ↦ t.values (x.1 • x.2))
  let b : E → P.obj (op N.1) := Sum.elim
    (fun x ↦ t.values x.1 + t.values x.2) (fun x ↦ x.1 • t.values x.2)
  have h (e : E) : Φ.toPresheafFiber N.1 N.2 P (a e) =
      Φ.toPresheafFiber N.1 N.2 P (b e) := by
    rcases e with ⟨x, y⟩ | ⟨r, x⟩
    · change Φ.toPresheafFiber t.U t.point P (t.values (x + y)) =
        Φ.toPresheafFiber t.U t.point P (t.values x + t.values y)
      simp only [map_add, t.germ_eq]
    · change Φ.toPresheafFiber t.U t.point P (t.values (r • x)) =
        Φ.toPresheafFiber t.U t.point P (r • t.values x)
      simp only [map_smul, t.germ_eq]
  let q (e : E) := Φ.equalityRefinement P N (a e) (b e) (h e)
  let c := IsCofiltered.wideCospan (fun e : E ↦ (q e).map)
  let W := c.choose
  let g : W ⟶ N := c.choose_spec.choose
  let k (e : E) : W ⟶ (q e).neighborhood := c.choose_spec.choose_spec.choose e
  have comm (e : E) : k e ≫ (q e).map = g := c.choose_spec.choose_spec.choose_spec e
  have eqn (e : E) : P.map g.val.op (a e) = P.map g.val.op (b e) := by
    have he := congrArg (fun z ↦ P.map (k e).val.op z) (q e).eq_map
    have hg : (k e).val ≫ (q e).map.val = g.val := congrArg Subtype.val (comm e)
    simpa only [← ModuleCat.comp_apply, ← P.map_comp, ← op_comp, hg] using he
  let l : M ⟶ P.obj (op W.1) := ModuleCat.ofHom
    { toFun := fun x ↦ P.map g.val.op (t.values x)
      map_add' := fun x y ↦ by
        simpa only [a, b, Sum.elim_inl, map_add] using eqn (Sum.inl (x, y))
      map_smul' := fun r x ↦ by
        simpa only [a, b, Sum.elim_inr, map_smul, RingHom.id_apply] using eqn (Sum.inr (r, x)) }
  exact
    { U := W.1
      point := W.2
      map := l
      map_germ := by
        ext x
        have hx := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w g.val W.2 P) (t.values x)
        rw [g.property] at hx
        exact hx.trans (t.germ_eq x) }

/-- Over a finite ring every finitely generated module admits an actual local lift into sections. -/
def linearLift [Finite R] (M : ModuleCat.{m} R) [Module.Finite R M]
    (f : M ⟶ (Φ.presheafFiber (A := ModuleCat.{m} R)).obj P) : LinearLift Φ P M f := by
  letI : Finite M := Module.finite_of_finite (R := R)
  exact Φ.linearLiftOfFinite P M f

end CategoryTheory.GrothendieckTopology.Point
