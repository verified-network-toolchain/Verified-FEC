(*In separate file because we want both in CommonVST and ReedSolomonList, and CommonVST purposely has
  no dependencies on any other files*) 
Require Import VST.floyd.functional_base.
Instance Inhabitant_option: forall {A: Type}, Inhabitant (option A).
intros A. apply None.
Defined.