module

public import Mathlib.CategoryTheory.Action
public import Mathlib.LinearAlgebra.BilinearMap
public import stacks_project.Chap97.Lemma_97_13_1_FixOne
public import stacks_project.Chap97.«97_13_0_2_Functor»

/-!
# Action groupoid of unit-fixing automorphisms on free algebras

The source conjugation formula defines a right action of `glFixOne R d`.
We realize it as a left action of the opposite group, retaining the original
matrix coordinates on arrows. This corrects the source's multiplication order
without changing the contravariant algebra-map convention of `FA`.
The resulting groupoid fibres assemble into a functor
`Schemeᵒᵖ ⥤ Grpd`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FreeDimAlgebra

variable {R : Type u} [CommRing R] {d : ℕ} [NeZero d]

/-- Conjugation of a free `d`-dimensional algebra by a unit-fixing automorphism:
the multiplication of `conjugate g m` is `g⁻¹ ∘ m.mul ∘ (g ⊗ g)`. -/
def conjugate (g : glFixOne R d) (m : FreeDimAlgebra R d) : FreeDimAlgebra R d where
  mul := (m.mul.compl₁₂ g.val.val g.val.val).compr₂ g.val.inv
  mul_assoc := sorry
  mul_comm := sorry
  one_mul := sorry

/-- The multiplication of `conjugate g m` is `g⁻¹ ∘ m.mul ∘ (g ⊗ g)`. -/
theorem conjugate_mul (g : glFixOne R d) (m : FreeDimAlgebra R d) (x y : Fin d → R) :
    (conjugate g m).mul x y = g.val.inv (m.mul (g.val.val x) (g.val.val y)) :=
  sorry

/-- The opposite group acts by the source's right-conjugation formula. -/
instance instMulActionFreeDimAlgebra : MulAction (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d) where
  smul g m := conjugate g.unop m
  one_smul := sorry
  mul_smul := sorry

/-- The action of `g` on `m` is conjugation of multiplication. -/
theorem smul_def (g : glFixOne R d) (m : FreeDimAlgebra R d) :
    MulOpposite.op g • m = conjugate g m :=
  sorry

end FreeDimAlgebra

namespace FA

/-- The fibre functor sending a free `d`-dimensional algebra to the corresponding
object of the action groupoid. -/
def toAction (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    FreeDimAlgebra R d ⥤ ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d) where
  obj m := (m : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d))
  map φ := ⟨MulOpposite.op ⟨φ.equiv, φ.map_one⟩, sorry⟩
  map_id := sorry
  map_comp := sorry

/-- `toAction` is the identity on the underlying free algebras. -/
theorem toAction_obj {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (m : FreeDimAlgebra R d) :
    ActionCategory.back ((toAction R d).obj m) = m :=
  sorry

/-- The inverse fibre functor, recovering a free `d`-dimensional algebra from an
object of the action groupoid. -/
def fromAction (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d) ⥤ FreeDimAlgebra R d where
  obj := ActionCategory.back
  map f := FreeDimAlgebra.Hom.of (MulOpposite.unop f.val).val
    (MulOpposite.unop f.val).property sorry
  map_id := sorry
  map_comp := sorry

/-- `fromAction` is `ActionCategory.back` on objects. -/
theorem fromAction_obj {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (m : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d)) :
    (fromAction R d).obj m = ActionCategory.back m :=
  sorry

/-- Base change of rings induces a functor of action groupoids. -/
def mapAction {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d] (f : R →+* S) :
    ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d) ⥤
      ActionCategory (glFixOne S d)ᵐᵒᵖ (FreeDimAlgebra S d) where
  obj m :=
    (FreeDimAlgebra.baseChange f (ActionCategory.back m) :
      ActionCategory (glFixOne S d)ᵐᵒᵖ (FreeDimAlgebra S d))
  map φ := ⟨MulOpposite.op (GLFixOne.map f (MulOpposite.unop φ.val)), sorry⟩
  map_id := sorry
  map_comp := sorry

/-- On objects, `mapAction f` is base change of the underlying free algebra. -/
theorem mapAction_obj {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]
    (f : R →+* S) (m : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d)) :
    ActionCategory.back ((mapAction f).obj m) =
      FreeDimAlgebra.baseChange f (ActionCategory.back m) :=
  sorry

/-- The functor in groupoids sending a scheme `T` to the action groupoid of
`(glFixOne Γ(T, ⊤) d)ᵐᵒᵖ` on `FreeDimAlgebra Γ(T, ⊤) d`. -/
def actionGroupoid (d : ℕ) [NeZero d] : Scheme.{u}ᵒᵖ ⥤ Grpd.{u, u} where
  obj T :=
    Grpd.of (ActionCategory (glFixOne Γ(T.unop, ⊤) d)ᵐᵒᵖ (FreeDimAlgebra Γ(T.unop, ⊤) d))
  map f := mapAction (Scheme.Γ.map f).hom
  map_id := sorry
  map_comp := sorry

/-- The value of `actionGroupoid d` at a scheme `T` is the action groupoid of
unit-fixing automorphisms on free `d`-dimensional algebras over `Γ(T, ⊤)`. -/
theorem actionGroupoid_obj (d : ℕ) [NeZero d] (T : Scheme.{u}) :
    (actionGroupoid d).obj (op T) =
      Grpd.of (ActionCategory (glFixOne Γ(T, ⊤) d)ᵐᵒᵖ (FreeDimAlgebra Γ(T, ⊤) d)) :=
  sorry

/-- Restriction of `actionGroupoid d` along a morphism of schemes is `mapAction`
of the induced map on global sections. -/
theorem actionGroupoid_map (d : ℕ) [NeZero d] {T T' : Scheme.{u}ᵒᵖ} (f : T ⟶ T') :
    (actionGroupoid d).map f = mapAction (Scheme.Γ.map f).hom :=
  sorry

/-- The fibrewise isomorphism between the groupoid of free `d`-dimensional algebras
and the corresponding action groupoid. -/
def fibreIso (d : ℕ) [NeZero d] (T : Scheme.{u}ᵒᵖ) :
    (FA d).obj T ≅ (actionGroupoid d).obj T where
  hom := toAction Γ(T.unop, ⊤) d
  inv := fromAction Γ(T.unop, ⊤) d
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward component of `fibreIso` is `toAction`. -/
theorem fibreIso_hom (d : ℕ) [NeZero d] (T : Scheme.{u}ᵒᵖ) :
    (fibreIso d T).hom = toAction Γ(T.unop, ⊤) d :=
  sorry

/-- An isomorphism of free `d`-dimensional algebras corresponds to a unique
unit-fixing automorphism sending the source to the target under conjugation. -/
def homEquiv {R : Type u} [CommRing R] {d : ℕ} [NeZero d] (m m' : FreeDimAlgebra R d) :
    (m ⟶ m') ≃ {g : glFixOne R d // FreeDimAlgebra.conjugate g m = m'} where
  toFun φ := ⟨⟨φ.equiv, φ.map_one⟩, sorry⟩
  invFun g := FreeDimAlgebra.Hom.of g.1.val g.1.property sorry
  left_inv := sorry
  right_inv := sorry

/-- The underlying automorphism of `homEquiv` is the equivalence of the isomorphism. -/
theorem homEquiv_apply {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    {m m' : FreeDimAlgebra R d} (φ : m ⟶ m') :
    (homEquiv m m' φ).1.val = φ.equiv :=
  sorry

/-- Arrows of the fibre groupoid are pairs `(g, m)` with source `m` and target `conjugate g m`. -/
def arrowEquiv (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    glFixOne R d × FreeDimAlgebra R d ≃
      (Σ m : FreeDimAlgebra R d, Σ m' : FreeDimAlgebra R d, m ⟶ m') where
  toFun p := ⟨p.2, FreeDimAlgebra.conjugate p.1 p.2, (homEquiv p.2 (FreeDimAlgebra.conjugate p.1 p.2)).symm ⟨p.1, sorry⟩⟩
  invFun p := ⟨(homEquiv p.1 p.2.1) p.2.2, p.1⟩
  left_inv := sorry
  right_inv := sorry

/-- The source of the arrow corresponding to `(g, m)` is `m`. -/
theorem arrowEquiv_source {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (g : glFixOne R d) (m : FreeDimAlgebra R d) :
    (arrowEquiv R d (g, m)).1 = m :=
  sorry

/-- The target of the arrow corresponding to `(g, m)` is `g • m`. -/
theorem arrowEquiv_target {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (g : glFixOne R d) (m : FreeDimAlgebra R d) :
    (arrowEquiv R d (g, m)).2.1 = FreeDimAlgebra.conjugate g m :=
  sorry

end FA

end AlgebraicGeometry
