module

public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap67.Lemma_67_23_2
public import stacks_project.Chap67.Lemma_67_23_7
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap71.Definition_71_17_1_Rees
public import stacks_project.Chap76.«76_42_5_1_ProperSupport»

/-!
# Closed subspaces cut out by powers of an ideal sheaf

This file records the closed subspace `V(K^e)`, the inverse-image ideal
`I 𝒪_{V(K^e)}`, and the restricted proper-support completion functor on that
thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The closed subspace cut out by a quasi-coherent ideal sheaf is Noetherian
when the ambient algebraic space is Noetherian. -/
instance instIsNoetherian_ofQuasiCoherentIdeal
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    IsNoetherian (ClosedSubspace.ofQuasiCoherentIdeal I).X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Powers of a quasi-coherent ideal sheaf remain quasi-coherent. -/
instance instIsQuasiCoherent_pow (K : IdealSubobject X) [IsQuasiCoherent K]
    (e : ℕ) : IsQuasiCoherent (K ^ e) :=
  sorry

/-- The closed subspace of `X` cut out by a power of a quasi-coherent ideal
sheaf. -/
noncomputable def idealPowerClosedSubspace (K : IdealSubobject X)
    [IsQuasiCoherent K] (e : ℕ) : ClosedSubspace X :=
  ClosedSubspace.ofQuasiCoherentIdeal (K ^ e)

/-- The closed subspace cut out by `K ^ e` is Noetherian when `X` is. -/
instance instIsNoetherian_idealPowerClosedSubspace (K : IdealSubobject X)
    [IsQuasiCoherent K] [IsNoetherian X] (e : ℕ) :
    IsNoetherian (idealPowerClosedSubspace K e).X :=
  sorry

/-- `idealPowerClosedSubspace K e` is the closed subspace cut out by `K ^ e`. -/
theorem idealPowerClosedSubspace_eq (K : IdealSubobject X)
    [IsQuasiCoherent K] (e : ℕ) :
    idealPowerClosedSubspace K e = ClosedSubspace.ofQuasiCoherentIdeal (K ^ e) :=
  sorry

/-- The inclusion of `idealPowerClosedSubspace K e` is the closed-subspace
inclusion of `K ^ e`. -/
theorem idealPowerClosedSubspace_ι (K : IdealSubobject X)
    [IsQuasiCoherent K] (e : ℕ) :
    (idealPowerClosedSubspace K e).ι = subschemeι (K ^ e) :=
  sorry

/-- The inverse-image ideal `I 𝒪_{V(K^e)}` on the closed subspace cut out by
`K ^ e`. -/
noncomputable def idealPowerPullback (I K : IdealSubobject X)
    [IsQuasiCoherent K] (e : ℕ) :
    IdealSubobject (idealPowerClosedSubspace K e).X :=
  I.pullback (idealPowerClosedSubspace K e).ι

/-- Inverse image of a quasi-coherent ideal along the inclusion of `V(K^e)` is
quasi-coherent. -/
instance instIsQuasiCoherent_idealPowerPullback (I K : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent K] (e : ℕ) :
    IsQuasiCoherent (idealPowerPullback I K e) :=
  sorry

/-- `idealPowerPullback I K e` is the inverse image of `I` along the inclusion of
`V(K^e)`. -/
theorem idealPowerPullback_eq (I K : IdealSubobject X)
    [IsQuasiCoherent K] (e : ℕ) :
    idealPowerPullback I K e = I.pullback (idealPowerClosedSubspace K e).ι :=
  sorry

/-- The inclusion of `V(K^e)` is a closed immersion, hence locally of finite
type. -/
instance instIsClosedImmersion_idealPowerClosedSubspace_ι (K : IdealSubobject X)
    [IsQuasiCoherent K] (e : ℕ) :
    IsClosedImmersion (idealPowerClosedSubspace K e).ι :=
  sorry

/-- The inclusion of `V(K^e)` is locally of finite type. -/
instance instLocallyOfFiniteType_idealPowerClosedSubspace_ι
    (K : IdealSubobject X) [IsQuasiCoherent K] (e : ℕ) :
    LocallyOfFiniteType (idealPowerClosedSubspace K e).ι :=
  sorry

/-- The composite of the inclusion of `V(K^e)` with a locally finite type
morphism remains locally of finite type. -/
instance instLocallyOfFiniteType_idealPowerClosedSubspace_ι_comp
    (f : X ⟶ Y) [LocallyOfFiniteType f] (K : IdealSubobject X)
    [IsQuasiCoherent K] (e : ℕ) :
    LocallyOfFiniteType ((idealPowerClosedSubspace K e).ι ≫ f) :=
  sorry

/-- Restricted proper-support completion on the closed subspace cut out by a
positive power of `K`, along the inverse-image ideal of `I`. -/
noncomputable def idealPowerCompletionFunctor (f : X ⟶ Y)
    (I K : IdealSubobject X)
    [IsNoetherian X] [LocallyOfFiniteType f]
    [IsQuasiCoherent I] [IsQuasiCoherent K] (e : ℕ+) :
    CoherentProperSupportOver
        ((idealPowerClosedSubspace K (e : ℕ)).ι ≫ f) ⥤
      CoherentFormalProperSupportOver
        ((idealPowerClosedSubspace K (e : ℕ)).ι ≫ f)
        (idealPowerPullback I K (e : ℕ)) :=
  coherentProperSupportCompletionFunctor
    ((idealPowerClosedSubspace K (e : ℕ)).ι ≫ f)
    (idealPowerPullback I K (e : ℕ))

/-- Restricted completion on `V(K^e)` is proper-support completion along
`I.pullback ι` for the composite `ι ≫ f`. -/
theorem idealPowerCompletionFunctor_eq (f : X ⟶ Y) (I K : IdealSubobject X)
    [IsNoetherian X] [LocallyOfFiniteType f]
    [IsQuasiCoherent I] [IsQuasiCoherent K] (e : ℕ+) :
    idealPowerCompletionFunctor f I K e =
      coherentProperSupportCompletionFunctor
        ((idealPowerClosedSubspace K (e : ℕ)).ι ≫ f)
        (idealPowerPullback I K (e : ℕ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
