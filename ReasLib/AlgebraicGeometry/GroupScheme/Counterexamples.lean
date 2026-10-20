module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.GroupScheme.Properties
public import ReasLib.AlgebraicGeometry.GroupScheme.RelativeIdentityComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.GroupScheme

/-- For every field, there is a flat group scheme of finite type over the affine line
whose structure morphism is not separated. -/
theorem exists_flat_finiteType_not_isSeparated_over_affineLine
    {k : Type u} [Field k] :
    ∃ G : GroupScheme (𝔸(ULift.{u} (Fin 1); Spec (CommRingCat.of k))),
      AlgebraicGeometry.Flat G.X.hom ∧ Scheme.Hom.FiniteType G.X.hom ∧
        ¬ AlgebraicGeometry.IsSeparated G.X.hom := sorry

/-- There is a group scheme over a scheme whose relative identity component is
flat over the base while the whole group scheme is not flat over the base. -/
theorem exists_identityComponent_flat_not_flat :
    ∃ (S : Scheme.{u}) (G : GroupScheme S) (hopen : IsOpen (identityComponentLocus G)),
      AlgebraicGeometry.Flat
          (Scheme.Opens.ι ⟨identityComponentLocus G, hopen⟩ ≫ G.X.hom) ∧
        ¬ AlgebraicGeometry.Flat G.X.hom := sorry

/-- For every field, there is a flat group scheme of finite type over countably
infinite-dimensional affine space whose structure morphism is not quasi-separated. -/
theorem exists_flat_finiteType_not_quasiSeparated_over_infiniteAffineSpace
    {k : Type u} [Field k] :
    ∃ G : GroupScheme (𝔸(ULift.{u} ℕ; Spec (CommRingCat.of k))),
      AlgebraicGeometry.Flat G.X.hom ∧ Scheme.Hom.FiniteType G.X.hom ∧
        ¬ AlgebraicGeometry.QuasiSeparated G.X.hom := sorry

end AlgebraicGeometry.GroupScheme
