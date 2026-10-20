module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/-!
# Definition 29.40.1

The reusable quasi-projective-morphism owners are maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective`.
-/

/- Definition 29.40.1: A morphism is quasi-projective when it is of finite type and admits a
relatively ample invertible module. -/
@[stacks 01VW] #check (AlgebraicGeometry.quasiProjective_iff :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S},
    QuasiProjective f ↔
      Scheme.Hom.FiniteType f ∧ ∃ L : X.Modules, RelativelyAmple f L)

#check (AlgebraicGeometry.hQuasiProjective_iff :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S},
    HQuasiProjective f ↔
      ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
        QuasiCompact i ∧ IsImmersion i ∧ i ≫ P.hom = f)

#check (AlgebraicGeometry.locallyQuasiProjective_iff :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S},
    LocallyQuasiProjective f ↔
      ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀,
        QuasiProjective (f ∣_ ((𝒰.f i).opensRange)))
