module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap78.Lemma_78_13_3_Intersection

/-!
# Coherence of the intersection with a pushforward

A quasi-compact, quasi-separated, flat, and surjective morphism of locally Noetherian
algebraic spaces pulls a coherent submodule of `f^* F` back to a coherent submodule of `F`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 78.13.3: Let `S` be a scheme, and let `f : Y ⟶ X` be a morphism of algebraic spaces
over `S`. Let `F` be a quasi-coherent `𝒪_X`-module, let `G` be a quasi-coherent `𝒪_Y`-module,
and let `φ : G ⟶ (pullback f).obj F` be an injective module map. If `f` is quasi-compact,
quasi-separated, flat, and surjective, `X` and `Y` are locally Noetherian, and `G` is coherent,
then `F ∩ f_* G`, defined as the pullback of the adjunction unit `F ⟶ f_* f^* F` along `f_* φ`,
is a coherent `𝒪_X`-module. -/
@[stacks 0GPR]
theorem isCoherent_intersectPushforward {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [Flat f] [Surjective f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {F : X.Modules} {G : Y.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] [G.IsCoherent]
    (φ : G ⟶ (pullback f).obj F) [Mono φ] :
    (intersectPushforward f φ).IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
