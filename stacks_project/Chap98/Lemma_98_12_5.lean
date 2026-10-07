module

public import stacks_project.Chap98.Definition_98_5_1
public import stacks_project.Chap98.Lemma_98_12_5_Hat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smoothness of the predeformation functor after a finite residue-field extension

In the setup of Definition 98.12.2, a finite residue-field extension of `u0`
induces a morphism of predeformation categories over `l`. If `X` satisfies (RS)
and `x` is versal at `u0`, that morphism is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 98.12.5: let `S`, `X`, `U`, `x`, `u0` be as in Definition 98.12.2.
Let `l` be a field and let `u_{l,0} = fromResidueExtension u0 l` be the
canonical morphism `Spec(l) ⟶ U` with image `u0` associated to a finite
extension `l / κ(u0)`. Set `x_{l,0} = residueExtensionObject hU x hx u0 l`.
If `X` satisfies (RS) and `x` is versal at `u0`, then
`ℱ_{(Sch/U)_fppf, l, u_{l,0}} ⟶ ℱ_{X, l, x_{l,0}}` is smooth. -/
@[stacks 07XG]
instance instIsSmooth_hatResidueExtension {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (l : Type u) [Field l]
    [Algebra Λ l] [Module.Finite Λ l] [Algebra (residueFieldType u0) l]
    [Module.Finite (residueFieldType u0) l]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ openImmersion =
        fromResidueExtension u0 l ≫ hU)
    [HasRimSchlessinger X] [IsVersalAt hU x hx u0] :
    BasedFunctor.IsSmooth
      (hatResidueExtension hU x hx u0 l openImmersion h_factor) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
