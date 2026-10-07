module

public import Mathlib.Data.Countable.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- For finite-type schemes `X` and `Y` over a finite-type scheme `S` over an
algebraically closed field, a countable family of finite-type base changes with
chosen isomorphisms covers every rational point where the fibers are isomorphic. -/
theorem exists_countable_finiteType_baseChange_isos
    {K : Type u} [Field K] [IsAlgClosed K]
    (S : SchemeOverField K) [Scheme.Hom.FiniteType S.hom]
    (X Y : Over S.left) [Scheme.Hom.FiniteType X.hom]
    [Scheme.Hom.FiniteType Y.hom] :
    ∃ I : Type u, Countable I ∧
      ∃ (Sᵢ : I → SchemeOverField K)
        (pᵢ : (i : I) → Sᵢ i ⟶ S)
        (hSᵢ : (i : I) → Scheme.Hom.FiniteType (pᵢ i).left)
        (hᵢ : (i : I) →
          (Over.pullback (pᵢ i).left).obj X ≅
            (Over.pullback (pᵢ i).left).obj Y),
        ∀ s : SchemeOverField.point K ⟶ S,
          Nonempty ((Over.pullback s.left).obj X ≅
            (Over.pullback s.left).obj Y) →
            ∃ (i : I) (q : SchemeOverField.point K ⟶ Sᵢ i),
              q ≫ pᵢ i = s := sorry

end AlgebraicGeometry.Scheme
