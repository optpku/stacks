module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Exactness
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Lemma 59.29.9 (1): the stalk functor on abelian étale presheaves is exact. -/
@[stacks 03PT] #check
  (AlgebraicGeometry.Scheme.Etale.presheafAbelianStalkExact :
    ∀ {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S),
      exactFunctor (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) AddCommGrpCat.{u}
        (Scheme.pointSmallEtale s).presheafFiber)

/- Lemma 59.29.9 (2): sheafification does not change the set-valued stalk at `s`. -/
@[stacks 03PT] #check
  (AlgebraicGeometry.Scheme.Etale.isIso_stalkMap_toSheafify :
    ∀ {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S) (F : S.Etaleᵒᵖ ⥤ Type u),
      IsIso ((Scheme.pointSmallEtale s).presheafFiber.map
        (toSheafify (Scheme.smallEtaleTopology S) F)))

/- Lemma 59.29.9 (3): the stalk functor on abelian étale sheaves is exact. -/
@[stacks 03PT] #check
  (AlgebraicGeometry.Scheme.Etale.sheafAbelianStalkExact :
    ∀ {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S),
      exactFunctor (Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u}) AddCommGrpCat.{u}
        (Scheme.pointSmallEtale s).sheafFiber)

/- Lemma 59.29.9 (4): the stalk functor on étale presheaves of sets is exact. -/
@[stacks 03PT] #check
  (AlgebraicGeometry.Scheme.Etale.presheafTypeStalkExact :
    ∀ {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S),
      exactFunctor (S.Etaleᵒᵖ ⥤ Type u) (Type u)
        (Scheme.pointSmallEtale s).presheafFiber)

/- Lemma 59.29.9 (5): the stalk functor on étale sheaves of sets is exact. -/
@[stacks 03PT] #check
  (AlgebraicGeometry.Scheme.Etale.sheafTypeStalkExact :
    ∀ {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S),
      exactFunctor (Sheaf (Scheme.smallEtaleTopology S) (Type u)) (Type u)
        (Scheme.pointSmallEtale s).sheafFiber)

/- Lemma 59.29.9 (6): the set-valued étale presheaf stalk functor preserves colimits. -/
@[stacks 03PT] #check
  (AlgebraicGeometry.Scheme.Etale.presheafTypeStalkPreservesColimits :
    ∀ {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S),
      PreservesColimits ((Scheme.pointSmallEtale s).presheafFiber :
        (S.Etaleᵒᵖ ⥤ Type u) ⥤ Type u))

/- Lemma 59.29.9 (7): the set-valued étale sheaf stalk functor preserves colimits. -/
@[stacks 03PT] #check
  (AlgebraicGeometry.Scheme.Etale.sheafTypeStalkPreservesColimits :
    ∀ {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S),
      PreservesColimits ((Scheme.pointSmallEtale s).sheafFiber :
        Sheaf (Scheme.smallEtaleTopology S) (Type u) ⥤ Type u))
