Object subclass: LObj [
  LObj class >> new: t [^super new]
]

LObj subclass: Nil [
  Nil class >> new [^super new]
  print [^'nil']
]

LObj subclass: Num [
  | num |
  Num class >> new: n [^super new setData: n; yourself]
  setData: n [num := n]
  data [^num]
  print [^num printString]
]

LObj subclass: Sym [
  | name |
  Sym class >> new: s [^super new setData: s; yourself]
  setData: s [name := s]
  data [^name]
  print [^name]
]

LObj subclass: Error [
  | msg |
  Error class >> new: s [^super new setData: s; yourself]
  setData: s [msg := s]
  data [^msg]
  print [^'<error: ', msg, '>']
]

LObj subclass: Cons [
  | ar dr |
  Cons class >> new: a with: d [^super new setData: a with: d; yourself]
  setData: a with: d [ar := a. dr := d]
  setCar: a [ar := a]
  setCdr: d [dr := d]
  car [^ar]
  cdr [^dr]
  print [
    | obj ret first |
    obj := self.
    ret := ''.
    first := true.
    [(obj class) = Cons] whileTrue: [
      first = true ifTrue: [
        first := false
      ] ifFalse: [
        ret := ret, ' '
      ].
      ret := ret, ((obj car) print).
      obj := obj cdr
    ].
    (obj class) = Nil ifTrue: [
      ^'(', ret, ')'
    ] ifFalse: [
      ^'(', ret, ' . ', (obj print), ')'
    ]
  ]
]

Object subclass: Util [
  kLPar :=  $(.
  kRPar :=  $).
  kQuote :=  $'.

  kNil := Nil new.
  symQuote := nil.

  Util class >> init [
    symQuote := self makeSym: 'quote'.
  ]

  symTable := Dictionary new.
  Util class >> makeSym: s [
    ^symTable at: s ifAbsent: [
      | sym |
      sym := Sym new: s.
      symTable at: s put: sym.
      ^sym
    ]
  ]

  Util class >> match: val with: clause default: def [
    ^((Dictionary from: clause) at: val ifAbsent: [def]) value
  ]

  Util class >> safeCar: obj [
    self match: obj class with: {
      Cons -> [^obj car]
    } default: [^kNil]
  ]

  Util class >> safeCdr: obj [
    self match: obj class with: {
      Cons -> [^obj cdr]
    } default: [^kNil]
  ]

  Util class >> nreverse: lst [
    | l tmp ret |
    l := lst.
    ret := kNil.
    [(l class) = Cons] whileTrue: [
      tmp := l cdr.
      l setCdr: ret.
      ret := l.
      l := tmp
    ].
    ^ret
  ]

  Util class >> isSpace: c [
    ^ (c = $<9>) | (c = $<10>) | (c = $<13>) | (c = $<32>)
  ]

  Util class >> isDelimiter: c [
    ^ (c = kLPar) | (c = kRPar) | (c = kQuote) | (self isSpace: c)
  ]

  Util class >> skipSpaces: s [
    | i done |
    i := 1.
    done := false.
    [(i <= s size) & (done not)] whileTrue: [
      (self isSpace: (s at: i)) ifTrue: [
        i := i + 1
      ] ifFalse: [
        done := true
      ]
    ].
    ^s copyFrom: i to: s size
  ]

  Util class >> makeNumOrSym: s [
    | num |
    num := s asInteger.
    (num printString) = s ifTrue: [
      ^Num new: num
    ] ifFalse: [
      ^self makeSym: s
    ]
  ]

  Util class >> readAtom: str [
    | s i done next |
    s := str.
    next := ''.
    i := 1.
    done := false.
    [(i <= s size) & (done not)] whileTrue: [
      (self isDelimiter: (s at: i)) ifTrue: [
        next := s copyFrom: i to: s size.
        s := (s copyFrom: 1 to: (i - 1)).
        done := true
      ] ifFalse: [
        i := i + 1
      ]
    ].
    ^{self makeNumOrSym: s. next}
  ]

  Util class >> read: str [
    | s tmp |
    s := self skipSpaces: str.
    (s size) = 0 ifTrue: [
      ^{Error new: 'empty input'. ''}
    ] ifFalse: [
      self match: (s at: 1) with: {
        kRPar -> [^{Error new: 'invalid syntax: ', s. ''}].
        kLPar -> [^self readList: (s copyFrom: 2 to: s size)].
        kQuote -> [
          tmp := self read: (s copyFrom: 2 to: s size).
          ^{Cons new: symQuote with: (Cons new: (tmp at: 1) with: kNil).
            tmp at: 2}
        ]
      } default: [^self readAtom: s]
    ]
  ]

  Util class >> readList: str [
    | s ret tmp |
    s := str.
    ret := kNil.
    [
      s := self skipSpaces: s.
      (s size) = 0 ifTrue: [
        ^{Error new: 'unfinished parenthesis'. ''}
      ] ifFalse: [
        (s at: 1) = kRPar ifTrue: [
          ^{self nreverse: ret. s copyFrom: 2 to: s size}
        ] ifFalse: [
          tmp := self read: s.
          ((tmp at: 1) class) = Error ifTrue: [
            ^tmp
          ] ifFalse: [
            ret := Cons new: (tmp at: 1) with: ret.
            s := tmp at: 2
          ]
        ]
      ]
    ] repeat
  ]
]

Object subclass: Lisp [
  Lisp class >> repl [
    | line |
    '> ' display.
    line := stdin nextLine.
    [line ~= nil] whileTrue: [
      ((Util read: line) at: 1) print displayNl.
      '> ' display.
      line := stdin nextLine.
    ]
  ]
]

Util init.
Lisp repl.
