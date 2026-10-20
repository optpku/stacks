/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.ArtinAxioms
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.OpennessOfVersality
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.Representability
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.RingTheory.Regular.GRing

/-!
# Algebraic spaces from Artin axioms on locally Noetherian schemes

Recognition of presheaves on locally Noetherian schemes as restrictions of
algebraic spaces, with uniqueness up to natural isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.StandardTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Over a locally Noetherian base whose finite-type-point stalks are G-rings,
a presheaf on locally Noetherian schemes with representable diagonal, uniformly
bounded finite-type-field values, the étale sheaf property, directed affine-limit
preservation, the Rim-Schlessinger property, finite-dimensional tangent spaces,
effective formal objects, and openness of versality extends to an algebraic
space. Its universe-raised presheaf of points is unique up to natural
isomorphism among algebraic spaces with the prescribed restriction. -/
theorem existsUnique_of_noetherianArtinAxioms {S : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian S]
    {F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (hΔ : uliftYoneda.{u + 1}.relativelyRepresentable (Limits.diag F))
    (h_size : Noetherian.boundedOnFiniteTypeFields F)
    (h0 : Presheaf.IsSheaf (locallyNoetherianTopology StandardTopology.etale S) F)
    (h1 : Extension.PreservesDirectedAffineLimits (locallyNoetherian S) F)
    [HasRimSchlessinger F] [HasFiniteDimensionalTangentSpaces F]
    [HasEffectiveFormalObjects F] [OpennessOfVersality F]
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    ∃ X : AlgebraicSpace S,
      Nonempty ((restrictPresheaf S).obj
        (AlgebraicGeometry.AlgebraicSpace.toSheaf.obj X).obj ≅ F) ∧
        ∀ Y : AlgebraicSpace S,
          Nonempty ((restrictPresheaf S).obj
            (AlgebraicGeometry.AlgebraicSpace.toSheaf.obj Y).obj ≅ F) →
            Nonempty ((AlgebraicGeometry.AlgebraicSpace.toSheaf.obj X).obj ≅
              (AlgebraicGeometry.AlgebraicSpace.toSheaf.obj Y).obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
