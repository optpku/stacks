/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
public import stacks_project.Chap67.Lemma_67_23_5
public import stacks_project.Chap67.Lemma_67_23_7
public import stacks_project.Chap69.Definition_69_12_1_Instances

/-!
# Coherent modules on scheme-theoretic supports

A coherent module on a locally Noetherian algebraic space is the pushforward of a
coherent module from any scheme-theoretic support. Closed immersions into locally
Noetherian algebraic spaces have locally Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The source of a closed immersion into a locally Noetherian algebraic space is
locally Noetherian. -/
theorem IsLocallyNoetherian.of_isClosedImmersion {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} [IsLocallyNoetherian X] (i : Z ⟶ X)
    [IsClosedImmersion i] : IsLocallyNoetherian Z :=
  sorry

/-- A closed subspace of a locally Noetherian algebraic space is locally
Noetherian. -/
instance instIsLocallyNoetherian_of_isClosedImmersion {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] (Z : ClosedSubspace X) :
    IsLocallyNoetherian Z.X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A quasi-coherent module on a scheme-theoretic support whose pushforward is
isomorphic to a coherent module is itself coherent. -/
theorem isCoherent_of_pushforward_iso {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] (i : Z ⟶ X)
    [IsSchemeTheoreticSupport F i] (G : Z.Modules) [G.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F) : G.IsCoherent :=
  sorry

namespace IsSchemeTheoreticSupport

/-- A coherent module on a locally Noetherian algebraic space is the pushforward of
a coherent module from any scheme-theoretic support. -/
theorem exists_coherent_module {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] (i : Z ⟶ X)
    [IsSchemeTheoreticSupport F i] :
    ∃ G : Z.Modules, G.IsCoherent ∧ Nonempty ((pushforward i).obj G ≅ F) :=
  sorry

end IsSchemeTheoreticSupport

/-- A quasi-coherent module on the scheme-theoretic support of a coherent module,
identified with that module after pushforward, is coherent. -/
theorem isCoherent_of_schemeTheoreticSupport {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (G : (schemeTheoreticSupport F).X.Modules) [G.IsQuasicoherent]
    (e : (pushforward (schemeTheoreticSupport F).ι).obj G ≅ F) : G.IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
