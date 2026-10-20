module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FinitePresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 70.9.3: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space over `S`. Let `F` be a finite type quasi-coherent `𝒪_X`-module. Then `F` is a filtered
colimit of finitely presented `𝒪_X`-modules with surjective transition maps. -/
@[stacks 086Y] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.exists_finitePresentation_colimitPresentation_epi :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent],
      ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
        ∃ pres : ColimitPresentation I F,
          (∀ i : I, (pres.diag.obj i).IsFinitePresentation) ∧
            ∀ {i i' : I} (f : i ⟶ i'), Epi (pres.diag.map f))
