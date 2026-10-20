module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.BaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.baseChangeOverDiagram :
  ∀ {C : Type u} [Category C] {S : Scheme.{u}}
    (D : C ⥤ AlgebraicSpace S) (i₀ : C)
    {T : AlgebraicSpace S} (t : T ⟶ D.obj i₀),
    Over i₀ ⥤ AlgebraicSpace S)
