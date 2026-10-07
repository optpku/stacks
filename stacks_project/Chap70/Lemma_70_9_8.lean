module

public import stacks_project.Chap70.Lemma_70_9_8_Extension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 70.9.8: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space over `S`. Let `U ⊂ X` be a quasi-compact open. Let `F` be a quasi-coherent `𝒪_X`-module.
Let `G ⊂ F|_U` be a quasi-coherent `𝒪_U`-submodule of finite type. Then there exists a
quasi-coherent finite-type submodule `G' ⊂ F` such that `G'|_U = G`. -/
@[stacks 0853] #check
  (exists_finiteTypeQuasiCoherentSubsheafExtension :
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (F : X.Modules) [F.IsQuasicoherent] (G : Subobject (restrict F j))
      [(G : U.Modules).IsQuasicoherent] [(G : U.Modules).IsFiniteType],
      ∃ H : Subobject F,
        (H : X.Modules).IsQuasicoherent ∧ (H : X.Modules).IsFiniteType ∧
          ∃ e : restrict (H : X.Modules) j ≅ (G : U.Modules),
            e.hom ≫ G.arrow = (restrictFunctor j).map H.arrow)
