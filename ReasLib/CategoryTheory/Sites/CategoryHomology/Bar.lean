/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bar category homology

This leaf owns the explicit composable-arrow bar construction and its functorial maps.  It is
independent of projective resolutions and derived categories; the comparison with derived-colimit
homology lives in `CategoryHomology.Computation`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v u' v' u'' v'' w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryHomology

section Basic

variable [UnivLE.{max u v, w}]

/-- The map from the terminal object of the image chain to the terminal object of a chain. -/
@[stacks 08PG "terminal map of composable-arrow chains"]
abbrev terminalMap (C : Type u) [Category.{v} C] {Δ Δ' : SimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') (x : ComposableArrows C Δ.unop.len) :
    ((nerve C).map f x).right ⟶ x.right :=
  x.map (homOfLE (Fin.le_last _))

/-- The terminal map of an identity simplex morphism is the identity. -/
@[stacks 08PG "terminal map identity law"]
theorem terminalMap_id {Δ : SimplexCategoryᵒᵖ}
    (x : ComposableArrows C Δ.unop.len) :
    terminalMap C (𝟙 Δ) x = 𝟙 x.right := sorry

/-- Terminal maps compose along morphisms of simplices. -/
@[stacks 08PG "terminal map composition law"]
theorem terminalMap_comp {Δ₀ Δ₁ Δ₂ : SimplexCategoryᵒᵖ}
    (f : Δ₀ ⟶ Δ₁) (g : Δ₁ ⟶ Δ₂) (x : ComposableArrows C Δ₀.unop.len) :
    terminalMap C (f ≫ g) x =
      terminalMap C g ((nerve C).map f x) ≫ terminalMap C f x := sorry

/-- Example 21.39.2: the source-facing simplicial abelian group whose `n`-th term is the
coproduct of `ℱ(Uₙ)` over composable chains in `C`. -/
@[stacks 08PG "category homology bar simplicial object"]
noncomputable def simplicialObject
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    SimplicialObject AddCommGrpCat.{w} where
  obj Δ := ∐ fun x : ComposableArrows C Δ.unop.len ↦ ℱ.obj (op x.right)
  map := fun {Δ Δ'} f ↦
    Limits.Sigma.desc fun x : ComposableArrows C Δ.unop.len ↦
      ℱ.map (terminalMap C f x).op ≫
        Sigma.ι
          (fun y : ComposableArrows C Δ'.unop.len ↦ ℱ.obj (op y.right))
          ((nerve C).map f x)
  map_id := sorry
  map_comp := sorry

/-- Example 21.39.2: the explicit bar chain complex obtained from the alternating-face-map
functor. -/
@[stacks 08PG "category homology bar complex"]
noncomputable abbrev complex
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    ChainComplex AddCommGrpCat.{w} ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{w}).obj
    (simplicialObject ℱ)

end Basic

section Functoriality

variable {C' : Type u'} [Category.{v'} C']
variable [UnivLE.{max u v, w}] [UnivLE.{max u' v', w}]

/-- The image of a composable chain under a functor. -/
abbrev mappedChain (u : C' ⥤ C)
    {Δ : SimplexCategoryᵒᵖ} (x : ComposableArrows C' Δ.unop.len) :
    ComposableArrows C Δ.unop.len :=
  (u.mapComposableArrows Δ.unop.len).obj x

/-- A functor commutes with the simplicial nerve action on composable chains. -/
@[stacks 08PH "mapped composable chain naturality"]
theorem mappedChain_map (u : C' ⥤ C)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    (x : ComposableArrows C' Δ.unop.len) :
    mappedChain u ((nerve C').map f x) =
      (nerve C).map f (mappedChain u x) := sorry

/-- Functors preserve the terminal-arrow map of a composable chain. -/
@[stacks 08PH "mapped terminal map naturality"]
theorem mappedTerminalMap (u : C' ⥤ C)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    (x : ComposableArrows C' Δ.unop.len) :
    terminalMap C f (mappedChain u x) = u.map (terminalMap C' f x) := sorry

/-- The component of the simplicial map induced by `u` and a coefficient morphism `t`. -/
abbrev simplicialMapApp (u : C' ⥤ C)
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) (Δ : SimplexCategoryᵒᵖ) :
    (simplicialObject (C := C') ℱ').obj Δ ⟶
      (simplicialObject (C := C) ℱ).obj Δ :=
  Sigma.map' (fun x : ComposableArrows C' Δ.unop.len ↦ mappedChain u x)
    (fun x ↦ t.app (Opposite.op x.right))

/-- Naturality of the bar-simplicial map induced by `u` and `t`. -/
@[stacks 08PH "category homology simplicial map naturality"]
theorem simplicialMap_naturality (u : C' ⥤ C)
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (simplicialObject (C := C') ℱ').map f ≫ simplicialMapApp u t Δ' =
      simplicialMapApp u t Δ ≫ (simplicialObject (C := C) ℱ).map f := sorry

/-- The simplicial map on bar constructions induced by `u` and `t`. -/
@[stacks 08PH "category homology simplicial map"]
noncomputable def simplicialMap (u : C' ⥤ C)
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) :
    simplicialObject (C := C') ℱ' ⟶ simplicialObject (C := C) ℱ where
  app := simplicialMapApp u t
  naturality := fun {_ _} f ↦ simplicialMap_naturality u t f

/-- Example 21.39.3: the explicit bar-complex map induced by `u` and `t`. -/
@[stacks 08PH "category homology bar complex map"]
abbrev complexMap (u : C' ⥤ C)
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) :
      complex (C := C') ℱ' ⟶ complex (C := C) ℱ :=
  (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{w}).map
    (simplicialMap u t)

/-- Example 21.39.3: the homology map induced by the explicit bar construction. -/
@[stacks 08PH "category homology bar complex homology map"]
noncomputable abbrev homologyMap (u : C' ⥤ C)
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) (n : ℕ) :
    (complex (C := C') ℱ').homology n ⟶ (complex (C := C) ℱ).homology n :=
  HomologicalComplex.homologyMap (complexMap u t) n

end Functoriality

namespace Bar

section Basic

variable [UnivLE.{max u v, w}]

/-- The homology object of the explicit bar complex, without derived-functor hypotheses. -/
@[stacks 08PG "bar category homology object"]
noncomputable abbrev homology (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    AddCommGrpCat.{w} :=
  (complex ℱ).homology n

end Basic

section Functoriality

variable {C' : Type u'} [Category.{v'} C']
variable [UnivLE.{max u v, w}] [UnivLE.{max u' v', w}]

/-- The map on bar homology induced by a functor and a coefficient morphism. -/
@[stacks 08PH "bar category homology map"]
noncomputable abbrev map (u : C' ⥤ C)
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) (n : ℕ) :
    homology (C := C') ℱ' n ⟶ homology (C := C) ℱ n :=
  homologyMap u t n

/-- Bar homology is invariant under replacing the indexing functor by an isomorphic one. -/
@[stacks 08PH "bar category homology natural-isomorphism invariance"]
theorem map_eq_of_iso (u v : C' ⥤ C) (α : u ≅ v)
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) (t' : ℱ' ⟶ v.op ⋙ ℱ)
    (h : t' ≫ (Functor.isoWhiskerRight (NatIso.op α) ℱ).hom = t)
    (n : ℕ) :
    map u t n = map v t' n := sorry

/-- Canonical transport of a bar-homology map along an isomorphism of indexing functors. -/
@[stacks 08PH "bar category homology map transport"]
theorem map_iso (u v : C' ⥤ C) (α : u ≅ v)
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) (n : ℕ) :
    map u t n = map v (t ≫ (Functor.isoWhiskerRight (NatIso.op α) ℱ).inv) n := sorry

end Functoriality

section Laws

variable [UnivLE.{max u v, w}]

/-- Bar homology maps preserve identity functors and coefficient maps. -/
@[simp, stacks 08PH "bar category homology identity map"]
theorem map_id (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    map (C := C) (C' := C) (𝟭 C) (𝟙 ℱ) n = 𝟙 (homology (C := C) ℱ n) := sorry

variable {C' : Type u'} [Category.{v'} C']
variable {C'' : Type u''} [Category.{v''} C'']
variable [UnivLE.{max u' v', w}] [UnivLE.{max u'' v'', w}]

/-- Bar homology maps compose without projective-preservation assumptions. -/
@[simp, stacks 08PH "bar category homology composition map"]
theorem map_comp (u : C' ⥤ C) (v : C'' ⥤ C')
    {ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    {ℱ'' : C''ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ℱ' ⟶ u.op ⋙ ℱ) (s : ℱ'' ⟶ v.op ⋙ ℱ') (n : ℕ) :
    map (C := C) (C' := C'') (v ⋙ u)
        (s ≫ ((Functor.whiskeringLeft C''ᵒᵖ C'ᵒᵖ AddCommGrpCat.{w}).obj v.op).map t) n =
      map (C := C') (C' := C'') v s n ≫ map (C := C) (C' := C') u t n := sorry

end Laws

section Coefficients

variable [UnivLE.{max u v, w}]

/-- The degree-`n` bar-homology functor in the coefficient presheaf. -/
@[stacks 08PG "bar category homology coefficient functor"]
noncomputable def coefficientFunctor (n : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w} where
  obj ℱ := homology (C := C) ℱ n
  map t := map (C := C) (C' := C) (𝟭 C) t n
  map_id ℱ := map_id ℱ n
  map_comp := sorry

/-- Bar homology is additive in the coefficient presheaf. -/
@[stacks 08PG "additivity of bar category homology"]
instance coefficientFunctor.additive (n : ℕ) :
    (coefficientFunctor (C := C) n).Additive := sorry

/-- Evaluation of the bar category-homology coefficient functor on an object. -/
@[simp, stacks 08PG "bar category homology coefficient functor object formula"]
theorem coefficientFunctor_obj (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    (coefficientFunctor (C := C) n).obj ℱ = homology (C := C) ℱ n := sorry

/-- Evaluation of the bar category-homology coefficient functor on a morphism. -/
@[simp, stacks 08PG "bar category homology coefficient functor map formula"]
theorem coefficientFunctor_map
    {ℱ ℱ' : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (t : ℱ ⟶ ℱ') (n : ℕ) :
    (coefficientFunctor (C := C) n).map t =
      map (C := C) (C' := C) (𝟭 C) t n := sorry

end Coefficients

end Bar

end CategoryHomology

end CategoryTheory
