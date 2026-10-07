module

public import Mathlib.FieldTheory.IsSepClosed
public import stacks_project.Chap59.Definition_59_29_1_GeometricPoint
public import stacks_project.Chap61.Lemma_61_12_2_Cover

open AlgebraicGeometry CategoryTheory Scheme

universe u v

@[expose] public section

namespace AlgebraicGeometry.Scheme

/-- The source field of a geometric point is algebraically closed. -/
instance geometricPoint_isAlgClosed {S : Scheme.{u}} (s : GeometricPoint S) :
    IsAlgClosed s.K :=
  s.isAlgClosed

/-- If `f : X ⟶ S` is weakly étale and `Ω` is a separably closed field, then a morphism
`s : Spec (.of Ω) ⟶ S` whose image point is hit by `x : X` factors through `f` by a morphism
`l : Spec (.of Ω) ⟶ X` sending the unique point of `Spec (.of Ω)` to `x`. -/
lemma exists_fac_of_weaklyEtale_of_isSepClosed {X S : Scheme.{u}} (f : X ⟶ S) [WeaklyEtale f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) (x : X)
    (hx : f x = s default) :
    ∃ (l : Spec (.of Ω) ⟶ X), l ≫ f = s ∧ l default = x :=
  sorry

namespace GeometricPoint

/-- Lemma 61.18.3: if `s` is a geometric point of a scheme `S` and `{φ_i : S_i ⟶ S}` is a
pro-étale covering, then some `i` admits a lift of `s` through `φ_i`, i.e. a morphism
`s_i : Spec (.of s.K) ⟶ S_i` with `s_i ≫ φ_i = s.hom`. -/
@[stacks 0F6C]
theorem exists_lift_of_proetaleCovering {S : Scheme.{u}} (s : GeometricPoint S)
    {ι : Type v} (family : ι → Over S) (hcover : ProetaleCovering family) :
    ∃ (i : ι) (s_i : Spec (.of s.K) ⟶ (family i).left),
      s_i ≫ (family i).hom = s.hom :=
  sorry

/-- A geometric point of `S` lifts through some member of a bundled pro-étale cover of `S`. -/
theorem exists_lift_of_proetaleCover {S : Scheme.{u}} (s : GeometricPoint S)
    (𝒰 : ProetaleCover S) :
    ∃ (i : 𝒰.I₀) (s_i : Spec (.of s.K) ⟶ 𝒰.X i), s_i ≫ 𝒰.f i = s.hom :=
  sorry

/-- A pro-étale covering of `S` admits a geometric point of some member, packaged from a
same-field lift of `s` by `GeometricPoint.of`. -/
theorem exists_geometricPoint_of_proetaleCovering {S : Scheme.{u}} (s : GeometricPoint S)
    {ι : Type v} (family : ι → Over S) (hcover : ProetaleCovering family) :
    ∃ (i : ι) (s_i : Spec (.of s.K) ⟶ (family i).left),
      (GeometricPoint.of s.K s_i).hom ≫ (family i).hom = s.hom :=
  sorry

end GeometricPoint

end AlgebraicGeometry.Scheme
