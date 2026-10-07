module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Detection
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Forget
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Naturality
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.NatTrans
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable

/-!
# Cartesian morphisms in relative inertia

Aggregate entry point for the cartesian relative- and absolute-inertia API.
The implementation is organized into cartesian detection, heterogeneous forgetting, fibred maps
and comparison cells, local `2`-cell action, the absolute-inertia pseudofunctor, and
stable-universe forgetful/section transformations.

Import a leaf module when only one layer is required; this entry point remains
available for comprehensive existing uses.
-/

@[expose] public section
