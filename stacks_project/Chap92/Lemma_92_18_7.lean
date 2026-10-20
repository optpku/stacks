module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Product
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

universe u

/- Lemma 92.18.7. For homomorphisms A → B and A → B' of ring sheaves on a site, the
canonical comparison L(B × B' / A) → L(B/A) ⊕ L(B'/A) is an isomorphism in D(B × B'). -/
@[stacks 08SY] #check (SheafOfModules.RingedSite.CotangentComplex.prodMap_isIso :
  ∀ {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
    [HasWeakSheafify J CommRingCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
    {A B B' : Sheaf J CommRingCat.{u}}
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (ringSheaf J (B ⨯ B')))]
    (φ : A ⟶ B) (ψ : A ⟶ B'),
    IsIso (SheafOfModules.RingedSite.CotangentComplex.prodMap φ ψ))
