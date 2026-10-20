module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Strict
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.StrongTrans

/-!
# Fibred-inertia pseudofunctor

Compatibility aggregate for the strict and ordinary fibred-inertia pseudofunctor API. Import
`Cartesian.Map` and `Cartesian.NatTrans` directly when only the reusable typed action is needed.
Its owners are `Inertia.map`, `map₂`, `mapFunctor`, `mapIso`, `mapIdIso`, and `mapCompIso`;
strict and ordinary pseudofunctors contribute structural bridges, including
their on-the-nose `map_id` and `map_comp` computations. Import
`Cartesian.Pseudofunctor.StrongTrans` for the object-level forgetful and identity-section
transformations and their component/naturality API.

The relative theory on invertibly commuting squares is available through
`Cartesian.Pseudofunctor.Relative`, including its direct local action and the forgetful bridge
to the based pseudo-comma pseudofunctor.
-/
