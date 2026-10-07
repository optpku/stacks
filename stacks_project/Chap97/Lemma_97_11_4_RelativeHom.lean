module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_2_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Relative Hom sheaves of algebraic spaces

The sheaf `Mor_B(Z, X)` on the fppf site of schemes over `S`, whose value at `T`
is a morphism `a : T ⟶ B` together with a morphism `T ×_B Z ⟶ X` over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- View a morphism of algebraic spaces as a morphism of functors of points. -/
abbrev asFunctor {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    X.functorOfPoints ⟶ Y.functorOfPoints :=
  f

/-- Universe-raised functor of points of an algebraic space over `S`. -/
abbrev uliftFunctorOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}

/-- The universe-raised functor of points is an fppf sheaf on `Over S`. -/
theorem uliftFunctorOfPoints_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (uliftFunctorOfPoints X) :=
  sorry

/-- The fppf sheaf on `Over S` obtained by universe-raising the functor of points. -/
def uliftSheafOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨uliftFunctorOfPoints X, uliftFunctorOfPoints_isSheaf X⟩

/-- The underlying presheaf of `uliftSheafOfPoints X` is `uliftFunctorOfPoints X`. -/
theorem uliftSheafOfPoints_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (uliftSheafOfPoints X).obj = uliftFunctorOfPoints X :=
  rfl

namespace RelativeHom

variable {S : Scheme.{u}} {Z X B : AlgebraicSpace S}

/-- The functor of points of `T ×_B Z`, formed as the pullback of `a : T ⟶ B` and
`g : Z ⟶ B` in `((Over S)ᵒᵖ ⥤ Type u)`. -/
abbrev fiber {T : Over S} (a : ofOver T ⟶ B) (g : Z ⟶ B) : (Over S)ᵒᵖ ⥤ Type u :=
  Limits.pullback (asFunctor a) (asFunctor g)

/-- The first projection `T ×_B Z ⟶ T` of functors of points. -/
def fiberFst {T : Over S} (a : ofOver T ⟶ B) (g : Z ⟶ B) :
    fiber a g ⟶ (ofOver T).functorOfPoints :=
  Limits.pullback.fst (asFunctor a) (asFunctor g)

/-- The second projection `T ×_B Z ⟶ Z` of functors of points. -/
def fiberSnd {T : Over S} (a : ofOver T ⟶ B) (g : Z ⟶ B) :
    fiber a g ⟶ Z.functorOfPoints :=
  Limits.pullback.snd (asFunctor a) (asFunctor g)

/-- The two projections out of `T ×_B Z` agree over `B`. -/
theorem fiber_condition {T : Over S} (a : ofOver T ⟶ B) (g : Z ⟶ B) :
    fiberFst a g ≫ asFunctor a = fiberSnd a g ≫ asFunctor g :=
  Limits.pullback.condition

/-- Compatibility of `asFunctor (ofOverMap φ ≫ a)` with the identity on `B`. -/
theorem fiberMap_fst_comm {T T' : Over S} (φ : T' ⟶ T) (a : ofOver T ⟶ B) :
    asFunctor (ofOverMap φ ≫ a) ≫ 𝟙 B.functorOfPoints =
      asFunctor (ofOverMap φ) ≫ asFunctor a :=
  Category.comp_id _

/-- Compatibility of `asFunctor g` with the identity on `B`. -/
theorem fiberMap_snd_comm (g : Z ⟶ B) :
    asFunctor g ≫ 𝟙 B.functorOfPoints = 𝟙 Z.functorOfPoints ≫ asFunctor g :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- The comparison `T' ×_B Z ⟶ T ×_B Z` induced by `φ : T' ⟶ T`. -/
def fiberMap {T T' : Over S} (φ : T' ⟶ T) (a : ofOver T ⟶ B) (g : Z ⟶ B) :
    fiber (ofOverMap φ ≫ a) g ⟶ fiber a g :=
  Limits.pullback.map (asFunctor (ofOverMap φ ≫ a)) (asFunctor g)
    (asFunctor a) (asFunctor g) (asFunctor (ofOverMap φ))
    (𝟙 Z.functorOfPoints) (𝟙 B.functorOfPoints)
    (fiberMap_fst_comm φ a) (fiberMap_snd_comm g)

/-- A `T`-point of `Mor_B(Z, X)`: a morphism `a : T ⟶ B` and a morphism
`b : T ×_B Z ⟶ X` over `B`. -/
structure Point (g : Z ⟶ B) (h : X ⟶ B) (T : Over S) : Type (u + 1) where
  /-- The morphism `a : T ⟶ B` over `S`. -/
  a : ofOver T ⟶ B
  /-- The morphism `b : T ×_B Z ⟶ X` of functors of points. -/
  b : fiber a g ⟶ X.functorOfPoints
  /-- The morphism `b` lies over `B`. -/
  w : b ≫ asFunctor h = fiberSnd a g ≫ asFunctor g

namespace Point

/-- Build a relative-Hom pair from a morphism `a : T ⟶ B` and a morphism
`b : T ×_B Z ⟶ X` over `B`. -/
def of {g : Z ⟶ B} {h : X ⟶ B} {T : Over S} (a : ofOver T ⟶ B)
    (b : fiber a g ⟶ X.functorOfPoints)
    (w : b ≫ asFunctor h = fiberSnd a g ≫ asFunctor g) :
    Point g h T where
  a := a
  b := b
  w := w

/-- A relative-Hom pair is a morphism `T ×_B Z ⟶ X` over `B`. -/
theorem spec {g : Z ⟶ B} {h : X ⟶ B} {T : Over S} (p : Point g h T) :
    p.b ≫ asFunctor h = fiberSnd p.a g ≫ asFunctor g :=
  p.w

/-- The functor-of-points element of `B` determined by the morphism `a`. -/
def a_elem {g : Z ⟶ B} {h : X ⟶ B} {T : Over S} (p : Point g h T) :
    B.functorOfPoints.obj (op T) :=
  yonedaEquiv (p.a : yoneda.obj T ⟶ B.functorOfPoints)

/-- Base change of a relative-Hom pair along `φ : T' ⟶ T` preserves the over-`B`
triangle. -/
theorem restrict_w {g : Z ⟶ B} {h : X ⟶ B} {T T' : Over S} (p : Point g h T)
    (φ : T' ⟶ T) :
    (fiberMap φ p.a g ≫ p.b) ≫ asFunctor h =
      fiberSnd (ofOverMap φ ≫ p.a) g ≫ asFunctor g :=
  sorry

/-- Base change of a pair `(a, b)` along `φ : T' ⟶ T`, sending `a` to `a ∘ φ` and
precomposing `b` with `T' ×_B Z ⟶ T ×_B Z`. -/
def restrict {g : Z ⟶ B} {h : X ⟶ B} {T T' : Over S} (p : Point g h T)
    (φ : T' ⟶ T) : Point g h T' :=
  of (ofOverMap φ ≫ p.a) (fiberMap φ p.a g ≫ p.b) (restrict_w p φ)

end Point

/-- The relative-Hom presheaf `Mor_B(Z, X)` on schemes over `S`. -/
def functor (g : Z ⟶ B) (h : X ⟶ B) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Point g h T.unop
  map {T T'} φ := TypeCat.ofHom fun (p : Point g h T.unop) ↦ p.restrict φ.unop
  map_id := sorry
  map_comp := sorry

/-- Evaluating the relative-Hom presheaf at `T` recovers the type of pairs over `T`. -/
theorem functor_obj (g : Z ⟶ B) (h : X ⟶ B) (T : Over S) :
    (functor g h).obj (op T) = Point g h T :=
  rfl

/-- The relative-Hom presheaf is an fppf sheaf on `Over S`. -/
theorem isSheaf (g : Z ⟶ B) (h : X ⟶ B) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (functor g h) :=
  sorry

/-- The relative-Hom sheaf `Mor_B(Z, X)` on `(Sch/S)_fppf`. -/
def sheaf (g : Z ⟶ B) (h : X ⟶ B) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨functor g h, isSheaf g h⟩

/-- Evaluating `sheaf g h` on `T` recovers the type of relative-Hom pairs over `T`. -/
theorem sheaf_obj (g : Z ⟶ B) (h : X ⟶ B) (T : Over S) :
    (sheaf g h).obj.obj (op T) = Point g h T :=
  rfl

/-- Postcomposition with `f : X ⟶ Z` preserves the over-`B` triangle. -/
theorem postcomp_w (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S} (p : Point g (f ≫ g) T) :
    (p.b ≫ asFunctor f) ≫ asFunctor g = fiberSnd p.a g ≫ asFunctor g :=
  (Category.assoc p.b (asFunctor f) (asFunctor g)).trans p.w

/-- Postcomposition with `f : X ⟶ Z` on relative-Hom pairs, sending `(a, b)` to
`(a, b ≫ f)`. -/
def postcompPoint (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S} (p : Point g (f ≫ g) T) :
    Point g g T :=
  Point.of p.a (p.b ≫ asFunctor f) (postcomp_w f g p)

/-- Postcomposition `Mor_B(Z, X) ⟶ Mor_B(Z, Z)` induced by `f : X ⟶ Z`. -/
def postcomp (f : X ⟶ Z) (g : Z ⟶ B) : sheaf g (f ≫ g) ⟶ sheaf g g :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun (p : Point g (f ≫ g) T.unop) ↦ postcompPoint f g p
      naturality := sorry }

/-- Components of `postcomp` are `postcompPoint`. -/
theorem postcomp_app (f : X ⟶ Z) (g : Z ⟶ B) (T : (Over S)ᵒᵖ) :
    (postcomp f g).hom.app T =
      TypeCat.ofHom fun (p : Point g (f ≫ g) T.unop) ↦ postcompPoint f g p :=
  rfl

/-- The identity of `Z_T` as a relative-Hom pair over `a : T ⟶ B`. -/
def idSectionPoint (g : Z ⟶ B) {T : Over S} (a : ofOver T ⟶ B) : Point g g T :=
  Point.of a (fiberSnd a g) rfl

/-- The identity section of `Z` on a universe-raised `B`-point. -/
def idSectionApp (g : Z ⟶ B) (T : (Over S)ᵒᵖ)
    (x : (uliftFunctorOfPoints B).obj T) : Point g g T.unop :=
  idSectionPoint g (yonedaEquiv.symm x.down)

/-- The identity section `id_Z : B ⟶ Mor_B(Z, Z)` of fppf sheaves. -/
def idSection (g : Z ⟶ B) : uliftSheafOfPoints B ⟶ sheaf g g :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom (idSectionApp g T)
      naturality := sorry }

/-- Components of `idSection` are `idSectionApp`. -/
theorem idSection_app (g : Z ⟶ B) (T : (Over S)ᵒᵖ) :
    (idSection g).hom.app T = TypeCat.ofHom (idSectionApp g T) :=
  rfl

/-- The pair `(pr_T, b)` out of `T ×_B Z` agrees over `B`, so it induces
`T ×_B Z ⟶ T ×_B X` over `T`. -/
theorem overT_condition {g : Z ⟶ B} {h : X ⟶ B} {T : Over S} (p : Point g h T) :
    fiberFst p.a g ≫ asFunctor p.a = p.b ≫ asFunctor h :=
  (fiber_condition p.a g).trans p.w.symm

/-- The source-facing map `T ×_B Z ⟶ T ×_B X` over `T` associated to a relative-Hom
pair. -/
def overT {g : Z ⟶ B} {h : X ⟶ B} {T : Over S} (p : Point g h T) :
    fiber p.a g ⟶ fiber p.a h :=
  Limits.pullback.lift (fiberFst p.a g) p.b (overT_condition p)

/-- `overT p` commutes with the projections to `T`. -/
theorem overT_fst {g : Z ⟶ B} {h : X ⟶ B} {T : Over S} (p : Point g h T) :
    overT p ≫ fiberFst p.a h = fiberFst p.a g :=
  Limits.pullback.lift_fst (fiberFst p.a g) p.b (overT_condition p)

/-- `overT p` recovers `b` on the projection to `X`. -/
theorem overT_snd {g : Z ⟶ B} {h : X ⟶ B} {T : Over S} (p : Point g h T) :
    overT p ≫ fiberSnd p.a h = p.b :=
  Limits.pullback.lift_snd (fiberFst p.a g) p.b (overT_condition p)

/-- The over-`T` map `T ×_B Z ⟶ T ×_B X` is the pair `(pr_T, b)`. -/
theorem overT_iff {g : Z ⟶ B} {h : X ⟶ B} {T : Over S} (p : Point g h T) :
    overT p ≫ fiberFst p.a h = fiberFst p.a g ∧
      overT p ≫ fiberSnd p.a h = p.b :=
  ⟨overT_fst p, overT_snd p⟩

end RelativeHom

end AlgebraicGeometry.AlgebraicSpace
