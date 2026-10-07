module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.FunctionSheaves
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.ZMod
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u v w

/- Definition 59.23.1 (1): the commutative structure sheaf has sections `Γ(T, ⊤)`.
Forgetting ring structure down to additive groups gives `G_a`, also denoted `𝒪_S`
or `G_{a, S}`. The big selector ranges over Zariski, étale, smooth, syntomic, and fppf. -/
@[stacks 03P4] #check
  (AlgebraicGeometry.StandardTopology.Big.commStructureSheaf :
    ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u}),
      Sheaf (τ.overTopology S) CommRingCat.{u})

/- SmallStandardTopology ranges only over Zariski and étale, the two small sites
of Section 59.20. -/
#check
  (AlgebraicGeometry.SmallStandardTopology.commStructureSheaf .zariski :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      Sheaf S.smallZariskiTopology CommRingCat.{u})

#check
  (AlgebraicGeometry.SmallStandardTopology.commStructureSheaf .etale :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      Sheaf S.smallEtaleTopology CommRingCat.{u})

/- Definition 59.23.1 (2): the units sheaf has sections `Γ(T, ⊤)ˣ` and is denoted
`𝒪_S⁎`, `G_m`, or `G_{m, S}`. -/
@[stacks 03P4] #check
  (AlgebraicGeometry.StandardTopology.Big.unitsSheaf :
    ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u}),
      Sheaf (τ.overTopology S) CommGrpCat.{u})

#check
  (AlgebraicGeometry.SmallStandardTopology.unitsSheaf .zariski :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      Sheaf S.smallZariskiTopology CommGrpCat.{u})

#check
  (AlgebraicGeometry.SmallStandardTopology.unitsSheaf .etale :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      Sheaf S.smallEtaleTopology CommGrpCat.{u})

/- Definition 59.23.1 (3): on any site, the constant sheaf `ℤ/nℤ` is the
sheafification of the constant presheaf with value `ℤ/nℤ`. -/
@[stacks 03P4] #check
  (CategoryTheory.constantZModSheaf :
    ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
      [HasWeakSheafify J AddCommGrpCat.{w}] (n : ℕ), Sheaf J AddCommGrpCat.{w})
