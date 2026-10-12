/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.FieldValuedPoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- A property of quasi-compact, quasi-separated schemes over a nonempty
quasi-compact, quasi-separated base has a field-valued witness if it holds on
the base, is invariant under thickenings, is preserved by directed inverse
limits with affine transition morphisms, and is inherited by one part of a
closed/open-complement decomposition. -/
theorem exists_fieldValuedPoint_of_qcqs_induction
    {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T] [Nonempty T]
    (P : ObjectProperty (Over T))
    (h_thickening :
      ∀ {T'' T' : Over T}
        [CompactSpace T''.left] [QuasiSeparatedSpace T''.left]
        [CompactSpace T'.left] [QuasiSeparatedSpace T'.left]
        (f : T'' ⟶ T') [IsThickening f.left],
        P T'' ↔ P T')
    (h_limit :
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over T) (c : Cone D),
        IsLimit c →
        (∀ i : I, CompactSpace (D.obj i).left) →
        (∀ i : I, QuasiSeparatedSpace (D.obj i).left) →
        CompactSpace c.pt.left →
        QuasiSeparatedSpace c.pt.left →
        (∀ {i i' : I} (hii' : i ≤ i'),
          IsAffineHom (D.map (homOfLE hii')).left) →
        (∀ i : I, P (D.obj i)) →
        P c.pt)
    (h_decomposition :
      ∀ {T' Z V : Over T}
        [CompactSpace T'.left] [QuasiSeparatedSpace T'.left]
        [CompactSpace Z.left] [QuasiSeparatedSpace Z.left]
        [CompactSpace V.left] [QuasiSeparatedSpace V.left]
        (i : Z ⟶ T') (j : V ⟶ T')
        [IsClosedImmersion i.left] [IsOpenImmersion j.left],
        Set.range j.left.base = (Set.range i.left.base)ᶜ →
        P T' → P V ∨ P Z) :
    P (Over.mk (𝟙 T)) → ∃ p : FieldValuedPoint T, P p.over := sorry

end AlgebraicGeometry.Scheme
