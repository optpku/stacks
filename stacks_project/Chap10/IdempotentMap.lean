module

public import ReasLib.Algebra.Group.Idempotent.Map
import StacksCheckRecall

@[expose] public section

/-!
# Chapter 10 Compatibility Facade

@stack 00J9

The neutral owner of the map on idempotent subtypes is
`ReasLib.Algebra.Group.Idempotent.Map`. This historical import path remains
available for the chapter and for downstream files that depend on it.
-/

@[stacks 00J9] #check RingHom.idempotentMap
@[stacks 00J9] #check RingHom.idempotentMap_apply
@[stacks 00J9] #check RingHom.idempotentMap_comp_apply
