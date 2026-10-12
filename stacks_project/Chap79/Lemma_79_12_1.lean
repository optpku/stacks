/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap65.Lemma_65_9_1
public import stacks_project.Chap79.Lemma_79_12_1_Hom

/-!
# The finite-part functor is an fppf sheaf

For a morphism of algebraic spaces `f : X ⟶ Y` over a scheme `S`, the
finite-part presheaf `(X/Y)_fin` is an fppf sheaf, and morphisms of fppf
sheaves `T ⟶ (X/Y)_fin` are the 04PC pairs over an algebraic space `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 79.12.1 (1): the finite-part presheaf `(X/Y)_fin` of a morphism
`f : X ⟶ Y` of algebraic spaces over a scheme `S` is a sheaf for the fppf
topology on `Sch/S`. -/
@[stacks 04PE]
theorem finitePart_isSheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (finitePart f) :=
  sorry

namespace FinitePart

/-- The fppf sheaf on `Sch/S` associated to the finite-part functor of `f`. -/
def sheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  ⟨finitePart f, finitePart_isSheaf f⟩

/-- The underlying presheaf of `FinitePart.sheaf f` is `finitePart f`. -/
theorem sheaf_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sheaf f).obj = finitePart f :=
  sorry

end FinitePart

/-- Lemma 79.12.1 (2): for an algebraic space `T` over `S`, there is a canonical
bijection between morphisms of fppf sheaves `T ⟶ (X/Y)_fin` and pairs `(a, Z)`
satisfying 04PC. -/
@[stacks 04PE]
def finitePart_homEquiv {S : Scheme.{u}} {X Y T : AlgebraicSpace S} (f : X ⟶ Y) :
    (toSheaf T ⟶ FinitePart.sheaf f) ≃ FinitePart.Descended f T :=
  Sheaf.homEquiv.trans (FinitePart.homEquiv f)

/-- Applying `finitePart_homEquiv` recovers the descended 04PC pair of the
underlying presheaf morphism. -/
theorem finitePart_homEquiv_apply {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (f : X ⟶ Y) (η : toSheaf T ⟶ FinitePart.sheaf f) :
    finitePart_homEquiv f η = FinitePart.Descended.ofHom (Sheaf.homEquiv η) :=
  sorry

/-- On a scheme `U` over `S`, morphisms of fppf sheaves `U ⟶ (X/Y)_fin` are
scheme-level finite-part pairs. -/
def finitePart_homEquiv_ofOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (U : Over S) :
    (toSheaf (ofOver U) ⟶ FinitePart.sheaf f) ≃ FinitePart.Point f U :=
  Sheaf.homEquiv.trans (yonedaEquiv.trans (finitePart_obj_equiv f U))

end AlgebraicGeometry.AlgebraicSpace
