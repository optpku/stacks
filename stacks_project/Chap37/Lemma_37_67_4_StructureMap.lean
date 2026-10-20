module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.StructureMap
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- The canonical structure morphism is owned by the reusable admissible-span API. -/
#check (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.toBase :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y)
    [AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan i j],
    pushout i.left j.left ⟶ S)

/- The first computation law is owned by the reusable admissible-span API. -/
#check (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.inl_toBase :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y)
    [AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan i j],
    pushout.inl i.left j.left ≫
      AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.toBase i j = X.hom)

/- The second computation law is owned by the reusable admissible-span API. -/
#check (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.inr_toBase :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y)
    [AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan i j],
    pushout.inr i.left j.left ≫
      AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.toBase i j = Y.hom)
