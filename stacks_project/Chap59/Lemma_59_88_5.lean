module

public import ReasLib.AlgebraicGeometry.Scheme.FieldValuedPoint.Induction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

/- Lemma 59.88.5 (0F06, explicit local correction): the printed statement
omits nonemptiness of the qcqs base. With a nonempty base, the three original
stability assumptions imply a field-valued witness. The property is allowed
to hold on empty schemes; the correction does not assume otherwise. -/
@[stacks 0F06]
#check (AlgebraicGeometry.Scheme.exists_fieldValuedPoint_of_qcqs_induction :
  {T : Scheme.{u}} → [CompactSpace T] → [QuasiSeparatedSpace T] → [Nonempty T] →
  (P : ObjectProperty (Over T)) →
  (∀ {T'' T' : Over T}
    [CompactSpace T''.left] [QuasiSeparatedSpace T''.left]
    [CompactSpace T'.left] [QuasiSeparatedSpace T'.left]
    (f : T'' ⟶ T') [IsThickening f.left], P T'' ↔ P T') →
  (∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over T) (c : Cone D),
    IsLimit c →
    (∀ i : I, CompactSpace (D.obj i).left) →
    (∀ i : I, QuasiSeparatedSpace (D.obj i).left) →
    CompactSpace c.pt.left → QuasiSeparatedSpace c.pt.left →
    (∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii')).left) →
    (∀ i : I, P (D.obj i)) → P c.pt) →
  (∀ {T' Z V : Over T}
    [CompactSpace T'.left] [QuasiSeparatedSpace T'.left]
    [CompactSpace Z.left] [QuasiSeparatedSpace Z.left]
    [CompactSpace V.left] [QuasiSeparatedSpace V.left]
    (i : Z ⟶ T') (j : V ⟶ T')
    [IsClosedImmersion i.left] [IsOpenImmersion j.left],
    Set.range j.left.base = (Set.range i.left.base)ᶜ → P T' → P V ∨ P Z) →
  P (Over.mk (𝟙 T)) → ∃ p : Scheme.FieldValuedPoint T, P p.over)
