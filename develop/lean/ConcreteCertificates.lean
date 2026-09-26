import AutomataCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0

namespace CloitreCollaboration.Certificate.Concrete

def adderTotalityLeftRows : Array (Array Nat) := #[#[1,29,29,29],#[2,29,29,29],#[3,29,29,29],#[3,4,5,6],#[7,29,8,29],#[9,10,29,29],#[11,29,29,29],#[12,29,13,29],#[14,29,29,29],#[15,16,29,29],#[17,29,29,29],#[18,29,29,29],#[19,29,20,29],#[21,29,29,29],#[22,29,29,29],#[23,24,29,29],#[25,29,29,29],#[26,29,29,29],#[27,29,29,29],#[3,28,5,28],#[9,28,29,29],#[15,28,29,29],#[23,28,29,29],#[3,4,28,28],#[7,29,28,29],#[12,29,28,29],#[19,29,28,29],#[3,28,28,28],#[29,29,29,29],#[29,29,29,29]]
def adderTotalityLeftFinal : Array Bool := #[false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false]
def adderTotalityLeft : Machine 4 30 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 30 ((adderTotalityLeftRows[q.val]!)[c.val]!)
  accept q := adderTotalityLeftFinal[q.val]!


def adderTotalityRightRows : Array (Array Nat) := #[#[1,2,2,39],#[3,4,5,6],#[7,39,39,39],#[8,9,10,2],#[11,39,6,39],#[12,6,39,39],#[39,39,39,39],#[13,39,39,39],#[8,9,10,14],#[15,39,16,39],#[17,18,39,39],#[19,39,2,39],#[20,2,39,39],#[21,39,39,39],#[22,39,39,39],#[23,39,24,39],#[25,39,39,39],#[26,27,39,39],#[28,39,39,39],#[29,39,5,39],#[30,4,39,39],#[0,6,6,39],#[31,39,39,39],#[29,39,32,39],#[33,39,39,39],#[34,39,39,39],#[30,35,39,39],#[36,39,39,39],#[37,39,39,39],#[8,6,10,6],#[8,9,6,6],#[38,39,39,39],#[17,6,39,39],#[26,6,39,39],#[30,6,39,39],#[15,39,6,39],#[23,39,6,39],#[29,39,6,39],#[8,6,6,6],#[39,39,39,39]]
def adderTotalityRightFinal : Array Bool := #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false]
def adderTotalityRight : Machine 4 40 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 40 ((adderTotalityRightRows[q.val]!)[c.val]!)
  accept q := adderTotalityRightFinal[q.val]!


def adderTotalityPairs : List (Fin 30 × Fin 40) := [(⟨0, by decide⟩, ⟨0, by decide⟩), (⟨1, by decide⟩, ⟨1, by decide⟩), (⟨29, by decide⟩, ⟨2, by decide⟩), (⟨29, by decide⟩, ⟨39, by decide⟩), (⟨2, by decide⟩, ⟨3, by decide⟩), (⟨29, by decide⟩, ⟨4, by decide⟩), (⟨29, by decide⟩, ⟨5, by decide⟩), (⟨29, by decide⟩, ⟨6, by decide⟩), (⟨29, by decide⟩, ⟨7, by decide⟩), (⟨3, by decide⟩, ⟨8, by decide⟩), (⟨29, by decide⟩, ⟨9, by decide⟩), (⟨29, by decide⟩, ⟨10, by decide⟩), (⟨29, by decide⟩, ⟨11, by decide⟩), (⟨29, by decide⟩, ⟨12, by decide⟩), (⟨29, by decide⟩, ⟨13, by decide⟩), (⟨4, by decide⟩, ⟨9, by decide⟩), (⟨5, by decide⟩, ⟨10, by decide⟩), (⟨6, by decide⟩, ⟨14, by decide⟩), (⟨29, by decide⟩, ⟨15, by decide⟩), (⟨29, by decide⟩, ⟨16, by decide⟩), (⟨29, by decide⟩, ⟨17, by decide⟩), (⟨29, by decide⟩, ⟨18, by decide⟩), (⟨29, by decide⟩, ⟨19, by decide⟩), (⟨29, by decide⟩, ⟨20, by decide⟩), (⟨29, by decide⟩, ⟨21, by decide⟩), (⟨7, by decide⟩, ⟨15, by decide⟩), (⟨8, by decide⟩, ⟨16, by decide⟩), (⟨9, by decide⟩, ⟨17, by decide⟩), (⟨10, by decide⟩, ⟨18, by decide⟩), (⟨11, by decide⟩, ⟨22, by decide⟩), (⟨29, by decide⟩, ⟨23, by decide⟩), (⟨29, by decide⟩, ⟨24, by decide⟩), (⟨29, by decide⟩, ⟨25, by decide⟩), (⟨29, by decide⟩, ⟨26, by decide⟩), (⟨29, by decide⟩, ⟨27, by decide⟩), (⟨29, by decide⟩, ⟨28, by decide⟩), (⟨29, by decide⟩, ⟨29, by decide⟩), (⟨29, by decide⟩, ⟨30, by decide⟩), (⟨29, by decide⟩, ⟨0, by decide⟩), (⟨12, by decide⟩, ⟨23, by decide⟩), (⟨13, by decide⟩, ⟨24, by decide⟩), (⟨14, by decide⟩, ⟨25, by decide⟩), (⟨15, by decide⟩, ⟨26, by decide⟩), (⟨16, by decide⟩, ⟨27, by decide⟩), (⟨17, by decide⟩, ⟨28, by decide⟩), (⟨18, by decide⟩, ⟨31, by decide⟩), (⟨29, by decide⟩, ⟨32, by decide⟩), (⟨29, by decide⟩, ⟨33, by decide⟩), (⟨29, by decide⟩, ⟨34, by decide⟩), (⟨29, by decide⟩, ⟨35, by decide⟩), (⟨29, by decide⟩, ⟨36, by decide⟩), (⟨29, by decide⟩, ⟨37, by decide⟩), (⟨29, by decide⟩, ⟨8, by decide⟩), (⟨29, by decide⟩, ⟨1, by decide⟩), (⟨19, by decide⟩, ⟨29, by decide⟩), (⟨20, by decide⟩, ⟨32, by decide⟩), (⟨21, by decide⟩, ⟨33, by decide⟩), (⟨22, by decide⟩, ⟨34, by decide⟩), (⟨23, by decide⟩, ⟨30, by decide⟩), (⟨24, by decide⟩, ⟨35, by decide⟩), (⟨25, by decide⟩, ⟨36, by decide⟩), (⟨26, by decide⟩, ⟨37, by decide⟩), (⟨27, by decide⟩, ⟨38, by decide⟩), (⟨29, by decide⟩, ⟨14, by decide⟩), (⟨29, by decide⟩, ⟨3, by decide⟩), (⟨28, by decide⟩, ⟨6, by decide⟩), (⟨29, by decide⟩, ⟨22, by decide⟩), (⟨29, by decide⟩, ⟨31, by decide⟩), (⟨29, by decide⟩, ⟨38, by decide⟩)]

theorem adderTotalityCertificate : Valid adderTotalityLeft adderTotalityRight adderTotalityPairs := by decide

theorem adderTotalityAllWords (w) : accepts adderTotalityLeft w → accepts adderTotalityRight w :=
  valid_implies_inclusion _ _ _ adderTotalityCertificate w

#print axioms adderTotalityAllWords

def graphTotalityLeftRows : Array (Array Nat) := #[#[1,9],#[2,9],#[3,9],#[3,4],#[5,9],#[6,9],#[7,9],#[3,8],#[9,9],#[9,9]]
def graphTotalityLeftFinal : Array Bool := #[false,false,false,true,true,true,true,true,true,false]
def graphTotalityLeft : Machine 2 10 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 10 ((graphTotalityLeftRows[q.val]!)[c.val]!)
  accept q := graphTotalityLeftFinal[q.val]!


def graphTotalityRightRows : Array (Array Nat) := #[#[0,1],#[2,6],#[3,6],#[4,6],#[0,5],#[6,6],#[6,6]]
def graphTotalityRightFinal : Array Bool := #[true,true,true,true,true,true,false]
def graphTotalityRight : Machine 2 7 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 7 ((graphTotalityRightRows[q.val]!)[c.val]!)
  accept q := graphTotalityRightFinal[q.val]!


def graphTotalityPairs : List (Fin 10 × Fin 7) := [(⟨0, by decide⟩, ⟨0, by decide⟩), (⟨1, by decide⟩, ⟨0, by decide⟩), (⟨9, by decide⟩, ⟨1, by decide⟩), (⟨2, by decide⟩, ⟨0, by decide⟩), (⟨9, by decide⟩, ⟨2, by decide⟩), (⟨9, by decide⟩, ⟨6, by decide⟩), (⟨3, by decide⟩, ⟨0, by decide⟩), (⟨9, by decide⟩, ⟨3, by decide⟩), (⟨4, by decide⟩, ⟨1, by decide⟩), (⟨9, by decide⟩, ⟨4, by decide⟩), (⟨5, by decide⟩, ⟨2, by decide⟩), (⟨9, by decide⟩, ⟨0, by decide⟩), (⟨9, by decide⟩, ⟨5, by decide⟩), (⟨6, by decide⟩, ⟨3, by decide⟩), (⟨7, by decide⟩, ⟨4, by decide⟩), (⟨8, by decide⟩, ⟨5, by decide⟩)]

theorem graphTotalityCertificate : Valid graphTotalityLeft graphTotalityRight graphTotalityPairs := by decide

theorem graphTotalityAllWords (w) : accepts graphTotalityLeft w → accepts graphTotalityRight w :=
  valid_implies_inclusion _ _ _ graphTotalityCertificate w

#print axioms graphTotalityAllWords

def candidateBoundLeftRows : Array (Array Nat) := #[#[1,9],#[2,9],#[3,9],#[3,4],#[5,9],#[6,9],#[7,9],#[3,8],#[9,9],#[9,9]]
def candidateBoundLeftFinal : Array Bool := #[false,false,false,true,true,true,true,true,true,false]
def candidateBoundLeft : Machine 2 10 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 10 ((candidateBoundLeftRows[q.val]!)[c.val]!)
  accept q := candidateBoundLeftFinal[q.val]!


def candidateBoundRightRows : Array (Array Nat) := #[#[0,1],#[2,6],#[3,6],#[4,6],#[0,5],#[6,6],#[6,6]]
def candidateBoundRightFinal : Array Bool := #[true,true,true,true,true,true,false]
def candidateBoundRight : Machine 2 7 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 7 ((candidateBoundRightRows[q.val]!)[c.val]!)
  accept q := candidateBoundRightFinal[q.val]!


def candidateBoundPairs : List (Fin 10 × Fin 7) := [(⟨0, by decide⟩, ⟨0, by decide⟩), (⟨1, by decide⟩, ⟨0, by decide⟩), (⟨9, by decide⟩, ⟨1, by decide⟩), (⟨2, by decide⟩, ⟨0, by decide⟩), (⟨9, by decide⟩, ⟨2, by decide⟩), (⟨9, by decide⟩, ⟨6, by decide⟩), (⟨3, by decide⟩, ⟨0, by decide⟩), (⟨9, by decide⟩, ⟨3, by decide⟩), (⟨4, by decide⟩, ⟨1, by decide⟩), (⟨9, by decide⟩, ⟨4, by decide⟩), (⟨5, by decide⟩, ⟨2, by decide⟩), (⟨9, by decide⟩, ⟨0, by decide⟩), (⟨9, by decide⟩, ⟨5, by decide⟩), (⟨6, by decide⟩, ⟨3, by decide⟩), (⟨7, by decide⟩, ⟨4, by decide⟩), (⟨8, by decide⟩, ⟨5, by decide⟩)]

theorem candidateBoundCertificate : Valid candidateBoundLeft candidateBoundRight candidateBoundPairs := by decide

theorem candidateBoundAllWords (w) : accepts candidateBoundLeft w → accepts candidateBoundRight w :=
  valid_implies_inclusion _ _ _ candidateBoundCertificate w

#print axioms candidateBoundAllWords

def recurrenceLanguageLeftRows : Array (Array Nat) := #[#[1,11],#[2,11],#[3,11],#[3,4],#[5,11],#[6,11],#[7,11],#[8,9],#[8,10],#[11,11],#[5,11],#[11,11]]
def recurrenceLanguageLeftFinal : Array Bool := #[false,false,false,false,false,true,true,true,true,true,true,false]
def recurrenceLanguageLeft : Machine 2 12 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 12 ((recurrenceLanguageLeftRows[q.val]!)[c.val]!)
  accept q := recurrenceLanguageLeftFinal[q.val]!


def recurrenceLanguageRightRows : Array (Array Nat) := #[#[0,1],#[2,7],#[3,7],#[4,7],#[5,6],#[5,1],#[7,7],#[7,7]]
def recurrenceLanguageRightFinal : Array Bool := #[false,true,true,true,true,true,true,false]
def recurrenceLanguageRight : Machine 2 8 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 8 ((recurrenceLanguageRightRows[q.val]!)[c.val]!)
  accept q := recurrenceLanguageRightFinal[q.val]!


def recurrenceLanguagePairs : List (Fin 12 × Fin 8) := [(⟨0, by decide⟩, ⟨0, by decide⟩), (⟨1, by decide⟩, ⟨0, by decide⟩), (⟨11, by decide⟩, ⟨1, by decide⟩), (⟨2, by decide⟩, ⟨0, by decide⟩), (⟨11, by decide⟩, ⟨2, by decide⟩), (⟨11, by decide⟩, ⟨7, by decide⟩), (⟨3, by decide⟩, ⟨0, by decide⟩), (⟨11, by decide⟩, ⟨3, by decide⟩), (⟨4, by decide⟩, ⟨1, by decide⟩), (⟨11, by decide⟩, ⟨4, by decide⟩), (⟨5, by decide⟩, ⟨2, by decide⟩), (⟨11, by decide⟩, ⟨5, by decide⟩), (⟨11, by decide⟩, ⟨6, by decide⟩), (⟨6, by decide⟩, ⟨3, by decide⟩), (⟨7, by decide⟩, ⟨4, by decide⟩), (⟨8, by decide⟩, ⟨5, by decide⟩), (⟨9, by decide⟩, ⟨6, by decide⟩), (⟨10, by decide⟩, ⟨1, by decide⟩)]

theorem recurrenceLanguageCertificate : Valid recurrenceLanguageLeft recurrenceLanguageRight recurrenceLanguagePairs := by decide

theorem recurrenceLanguageAllWords (w) : accepts recurrenceLanguageLeft w → accepts recurrenceLanguageRight w :=
  valid_implies_inclusion _ _ _ recurrenceLanguageCertificate w

#print axioms recurrenceLanguageAllWords

def differenceLanguageLeftRows : Array (Array Nat) := #[#[1,9],#[2,9],#[3,9],#[3,4],#[5,9],#[6,9],#[7,9],#[3,8],#[9,9],#[9,9]]
def differenceLanguageLeftFinal : Array Bool := #[false,false,false,true,true,true,true,true,true,false]
def differenceLanguageLeft : Machine 2 10 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 10 ((differenceLanguageLeftRows[q.val]!)[c.val]!)
  accept q := differenceLanguageLeftFinal[q.val]!


def differenceLanguageRightRows : Array (Array Nat) := #[#[1,2],#[1,3],#[4,12],#[5,12],#[6,12],#[7,12],#[8,12],#[9,12],#[10,12],#[1,11],#[1,2],#[12,12],#[12,12]]
def differenceLanguageRightFinal : Array Bool := #[false,true,false,true,false,true,false,true,false,true,true,true,false]
def differenceLanguageRight : Machine 2 13 where
  start := ⟨0, by decide⟩
  step q c := Fin.ofNat 13 ((differenceLanguageRightRows[q.val]!)[c.val]!)
  accept q := differenceLanguageRightFinal[q.val]!


def differenceLanguagePairs : List (Fin 10 × Fin 13) := [(⟨0, by decide⟩, ⟨0, by decide⟩), (⟨1, by decide⟩, ⟨1, by decide⟩), (⟨9, by decide⟩, ⟨2, by decide⟩), (⟨2, by decide⟩, ⟨1, by decide⟩), (⟨9, by decide⟩, ⟨3, by decide⟩), (⟨9, by decide⟩, ⟨4, by decide⟩), (⟨9, by decide⟩, ⟨12, by decide⟩), (⟨3, by decide⟩, ⟨1, by decide⟩), (⟨9, by decide⟩, ⟨5, by decide⟩), (⟨9, by decide⟩, ⟨6, by decide⟩), (⟨4, by decide⟩, ⟨3, by decide⟩), (⟨9, by decide⟩, ⟨7, by decide⟩), (⟨9, by decide⟩, ⟨8, by decide⟩), (⟨5, by decide⟩, ⟨5, by decide⟩), (⟨9, by decide⟩, ⟨9, by decide⟩), (⟨9, by decide⟩, ⟨10, by decide⟩), (⟨6, by decide⟩, ⟨7, by decide⟩), (⟨9, by decide⟩, ⟨1, by decide⟩), (⟨9, by decide⟩, ⟨11, by decide⟩), (⟨7, by decide⟩, ⟨9, by decide⟩), (⟨8, by decide⟩, ⟨11, by decide⟩)]

theorem differenceLanguageCertificate : Valid differenceLanguageLeft differenceLanguageRight differenceLanguagePairs := by decide

theorem differenceLanguageAllWords (w) : accepts differenceLanguageLeft w → accepts differenceLanguageRight w :=
  valid_implies_inclusion _ _ _ differenceLanguageCertificate w

#print axioms differenceLanguageAllWords

end CloitreCollaboration.Certificate.Concrete
