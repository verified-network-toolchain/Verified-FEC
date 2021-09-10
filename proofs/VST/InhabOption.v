(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

(*In separate file because we want both in CommonVST and ReedSolomonList, and CommonVST purposely has
  no dependencies on any other files*) 
(*TODO: remove this when I update VST*)
Require Import VST.floyd.functional_base.
Instance Inhabitant_option: forall {A: Type}, Inhabitant (option A).
intros A. apply None.
Defined.