module

public import ReasLib.CategoryTheory.Sites.Cech.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Topology.Sheaves.Presheaf

/-!
# Čech refinement maps

This module owns the natural maps on Čech cosimplicial objects and cochain complexes induced by
a morphism of formal coproducts.  The slice-category specialization is a thin wrapper around the
formal-coproduct construction.
-/

@[expose] public section

open CategoryTheory.Limits
open AlgebraicTopology

noncomputable section

universe w v v' u u'

namespace CategoryTheory

section Bridge

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
variable [HasFiniteProducts C]

/-- A morphism of formal coproducts induces a natural transformation of the associated Čech
cosimplicial-object functors. -/
noncomputable abbrev formalCoproductCechCosimplicialNatTransOfRefinement {ι κ : Type w}
    (refinement : ι → C) (family : κ → C)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C)) :=
  Functor.whiskerLeft (FormalCoproduct.evalOp C A)
    ((Functor.whiskeringLeft SimplexCategory ((FormalCoproduct C)ᵒᵖ) A).map
      ((FormalCoproduct.cechFunctor.map σ).rightOp))

/-- Evaluating the Čech cosimplicial refinement natural transformation at a presheaf gives the
map from the coarser family to the refinement. -/
abbrev formalCoproductCechCosimplicialMapOfRefinement {ι κ : Type w} (refinement : ι → C)
    (family : κ → C)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C))
    (F : Cᵒᵖ ⥤ A) :
    (FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.cech (FormalCoproduct.mk κ family))).obj F ⟶
    (FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.cech (FormalCoproduct.mk ι refinement))).obj F :=
  (formalCoproductCechCosimplicialNatTransOfRefinement refinement family σ).app F

/-- A formal-coproduct refinement induces a natural transformation of Čech cochain-complex
functors. -/
noncomputable abbrev formalCoproductCechComplexNatTransOfRefinement {ι κ : Type w}
    (refinement : ι → C) (family : κ → C)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C)) :=
  Functor.whiskerRight
    (formalCoproductCechCosimplicialNatTransOfRefinement refinement family σ)
    (alternatingCofaceMapComplex A)

/-- The Čech-complex natural transformation induced by a morphism from the refinement formal
coproduct to the coarser formal coproduct. -/
noncomputable abbrev cechComplexRefinementNatTrans {ι κ : Type w} (refinement : ι → C)
    (family : κ → C)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C)) :=
  formalCoproductCechComplexNatTransOfRefinement (A := A) refinement family σ

/-- Evaluating the Čech cochain-complex refinement natural transformation at a presheaf gives the
canonical complex morphism. -/
abbrev formalCoproductCechComplexMapOfRefinement {ι κ : Type w} (refinement : ι → C)
    (family : κ → C)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C))
    (F : Cᵒᵖ ⥤ A) :
    (cechComplexFunctor family).obj F ⟶
      (cechComplexFunctor refinement).obj F :=
  (formalCoproductCechComplexNatTransOfRefinement refinement family σ).app F

/-- In degree `n`, a Čech refinement map is the corresponding component of its underlying
cosimplicial refinement map. -/
@[simp] theorem formalCoproductCechComplexMapOfRefinement_f {ι κ : Type w}
    (refinement : ι → C) (family : κ → C)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C))
    (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    (formalCoproductCechComplexMapOfRefinement refinement family σ F).f n =
      (formalCoproductCechCosimplicialMapOfRefinement refinement family σ F).app
        (SimplexCategory.mk n) := sorry

/-- The Čech cochain maps induced by two parallel morphisms of formal coproducts are chain
homotopic.  Thus the map depends on the selected refinement only before passing to homotopy or
cohomology. -/
theorem formalCoproductCechComplexMapOfRefinement_homotopic {ι κ : Type w}
    (refinement : ι → C) (family : κ → C)
    (σ τ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C))
    (F : Cᵒᵖ ⥤ A) :
    _root_.homotopic A (ComplexShape.up ℕ)
      (formalCoproductCechComplexMapOfRefinement refinement family σ F)
      (formalCoproductCechComplexMapOfRefinement refinement family τ F) := sorry

/-- Parallel selected refinements induce the same map on every Čech cohomology object for which
the relevant homology objects exist. -/
theorem formalCoproductCechComplexMapOfRefinement_homologyMap_eq {ι κ : Type w}
    (refinement : ι → C) (family : κ → C)
    (σ τ : (FormalCoproduct.mk ι refinement : FormalCoproduct C) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct C))
    (F : Cᵒᵖ ⥤ A) (p : ℕ)
    [((cechComplexFunctor family).obj F).HasHomology p]
    [((cechComplexFunctor refinement).obj F).HasHomology p] :
    HomologicalComplex.homologyMap
        (formalCoproductCechComplexMapOfRefinement refinement family σ F) p =
      HomologicalComplex.homologyMap
        (formalCoproductCechComplexMapOfRefinement refinement family τ F) p := sorry


end Bridge

section

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
variable (U : C) [HasFiniteProducts (Over U)]
variable {ι κ : Type w}

/-- A refinement in `Over U` induces a natural transformation on Čech-complex functors after
restricting presheaves to the slice category. -/
abbrev cechComplexMapOfRefinementNatTrans (family : κ → Over U) (refinement : ι → Over U)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct (Over U)) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct (Over U))) :
    (restrictPresheafToOver (A := A) U ⋙ cechComplexFunctor family) ⟶
      (restrictPresheafToOver (A := A) U ⋙ cechComplexFunctor refinement) :=
  Functor.whiskerLeft (restrictPresheafToOver (A := A) U)
    (formalCoproductCechComplexNatTransOfRefinement refinement family σ)

/-- A refinement of two indexed families into `U` induces the canonical map from the Čech
complex of the coarser family to that of the refinement. -/
@[stacks 03F4]
abbrev cechComplexMapOfRefinement (family : κ → Over U) (refinement : ι → Over U)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct (Over U)) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct (Over U)))
    (F : Cᵒᵖ ⥤ A) :
    cechComplex U family F ⟶ cechComplex U refinement F :=
  (cechComplexMapOfRefinementNatTrans U family refinement σ).app F

/-- In degree `n`, the Čech refinement map in a slice is induced by the corresponding
formal-coproduct Čech cosimplicial map on the restricted presheaf. -/
@[simp] theorem cechComplexMapOfRefinement_f (family : κ → Over U) (refinement : ι → Over U)
    (σ : (FormalCoproduct.mk ι refinement : FormalCoproduct (Over U)) ⟶
      (FormalCoproduct.mk κ family : FormalCoproduct (Over U)))
    (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    (cechComplexMapOfRefinement U family refinement σ F).f n =
      (formalCoproductCechCosimplicialMapOfRefinement refinement family σ
        ((restrictPresheafToOver (A := A) U).obj F)).app
        (SimplexCategory.mk n) := sorry

end


end CategoryTheory

namespace CategoryTheory

open TopologicalSpace

variable {X : TopCat.{u}} {I J : Type v}

/-- An indexed open family `𝒱` refines `𝒰` along `t` when every `𝒱 j` is contained in
`𝒰 (t j)`.  The predicate is independent of coefficients and is shared by all Čech layers. -/
def IsRefinement (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I) : Prop :=
  ∀ j : J, 𝒱 j ≤ 𝒰 (t j)

/-- The formal-coproduct morphism induced by an indexed-open refinement. -/
def refinementHom (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t) :
    (⟨J, 𝒱⟩ : Limits.FormalCoproduct (Opens X)) ⟶
      (⟨I, 𝒰⟩ : Limits.FormalCoproduct (Opens X)) where
  f := t
  φ j := homOfLE (ht j)

/-- The natural transformation of Čech complexes induced by a refinement of indexed open
families. -/
noncomputable abbrev cechRefinementNatTrans (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t) :
    (cechComplexFunctor 𝒰 :
      X.Presheaf AddCommGrpCat ⥤ CochainComplex AddCommGrpCat ℕ) ⟶
      (cechComplexFunctor 𝒱 :
        X.Presheaf AddCommGrpCat ⥤ CochainComplex AddCommGrpCat ℕ) :=
  cechComplexRefinementNatTrans 𝒱 𝒰 (refinementHom 𝒰 𝒱 t ht)


end CategoryTheory
