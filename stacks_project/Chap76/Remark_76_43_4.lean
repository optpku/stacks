module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MorphismAlgebraization
import StacksCheckRecall

/-!
# Algebraization under weaker separation axioms

A compatible system of morphisms between the adic stages of algebraic spaces over a
complete Noetherian affine base algebraizes when the source is proper and the target
is quasi-separated and locally of finite type. Uniqueness is not claimed.
The question without a separation assumption on the target remains unresolved.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Remark 76.43.4: if `A` is Noetherian and `I`-adically complete, `S = Spec(A)`,
`S_n = AdicThickening.spec I n`, `X` and `Y` are algebraic spaces over `S` with stages
`X_n = AdicThickening.stage X I n` and `Y_n = AdicThickening.stage Y I n`, and a
compatible system of morphisms `g n : X_n ⟶ Y_n` over `S_n` is given, then whenever
`X ⟶ S` is proper and `Y ⟶ S` is quasi-separated and locally of finite type there
exists a morphism `G : X ⟶ Y` over `S` whose base change to `S_n` is `g n`.
The separated-target case follows from `QuasiSeparated.of_separated`. Uniqueness is
not claimed. -/
@[stacks 0GHK] #check (AlgebraicGeometry.AlgebraicSpace.exists_algebraizingHom_of_quasiSeparated :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Proper (SchemeRealization.toBase X)] [QuasiSeparated (SchemeRealization.toBase Y)]
    [LocallyOfFiniteType (SchemeRealization.toBase Y)]
    (g : ∀ n : ℕ+, AdicThickening.stage X I n ⟶ AdicThickening.stage Y I n)
    (h_over : ∀ n, g n ≫ AdicThickening.toSpec Y I n = AdicThickening.toSpec X I n)
    (h_compat : ∀ n,
      g n ≫ AdicThickening.transition Y I n =
        AdicThickening.transition X I n ≫ g (n + 1)),
    ∃ G : X ⟶ Y, ∀ n, g n = AdicThickening.stageMap I G n)
