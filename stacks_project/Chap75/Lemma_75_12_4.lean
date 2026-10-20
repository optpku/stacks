module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.InjectiveAcyclic
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 75.12.4 (1). Let `S` be a scheme. Let `X` be a Noetherian algebraic space
over `S`. If `J` is an injective object of `QCoh X`, then
`IsZero (cohomology U (Modules.restrict ((QCoh.inclusion X).obj J) j) p)` for `0 < p`
and every quasi-compact and quasi-separated algebraic space `U` étale over `X`. -/
@[stacks 09TL]
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.cohomology_restrict_isZero_of_injective :
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} [IsNoetherian X]
    (j : U ⟶ X) [Etale j] [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U]
    (J : QCoh X) [Injective J] {p : ℕ} (hp : 0 < p)
    [HasSheafify (smallEtaleTopology U) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology U) AddCommGrpCat.{u})],
    IsZero (cohomology U (Modules.restrict ((QCoh.inclusion X).obj J) j) p))

section

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 75.12.4 (2). Let `S` be a scheme. Let `X` be a Noetherian algebraic space
over `S`. If `J` is an injective object of `QCoh X`, then for any morphism
`f : X ⟶ Y` of algebraic spaces over `S` with `Y` quasi-separated we have
`IsZero (Modules.higherDirectImage f ((QCoh.inclusion X).obj J) p)` for `0 < p`. -/
@[stacks 09TL]
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.higherDirectImage_isZero_of_injective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsNoetherian X] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) (J : QCoh X) [Injective J]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    {p : ℕ} (hp : 0 < p),
    IsZero (Modules.higherDirectImage f ((QCoh.inclusion X).obj J) p))

end
