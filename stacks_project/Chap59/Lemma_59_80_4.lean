module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Normal.StrictHenselian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 59.80.4 (1): A separated étale morphism over an integral normal scheme with
separably closed function field is an indexed coproduct of open immersions. -/
@[stacks 09Z9] #check (AlgebraicGeometry.Scheme.Hom.separatedEtaleOpenDecomposition :
    ∀ {X U : Scheme.{u}} [IsIntegral X], X.isNormal →
      ∀ [IsSepClosed X.functionField] (f : U ⟶ X) [Etale f] [IsSeparated f],
    ∃ (ι : Type u) (V : ι → Scheme.{u}) (e : U ≅ ∐ V)
      (j : ∀ i, V i ⟶ X),
      (∀ i, IsOpenImmersion (j i)) ∧ e.hom ≫ Sigma.desc j = f)

/- Lemma 59.80.4 (2): Every stalk ring of an integral normal scheme with separably closed
function field is strictly henselian. -/
@[stacks 09Z9] #check (AlgebraicGeometry.Scheme.strictHenselianLocalRingStalk :
    ∀ (X : Scheme.{u}) [IsIntegral X], X.isNormal →
      ∀ [IsSepClosed X.functionField] (x : X),
        StrictHenselianLocalRing (X.presheaf.stalk x))
