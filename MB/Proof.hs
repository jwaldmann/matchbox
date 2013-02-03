{-# language OverloadedStrings #-}

module MB.Proof 

( module MB.Proof.Type
, rtoc, tox
)

where

import MB.Proof.Type
import MB.Proof.Doc () -- Pretty instance
import MB.Proof.CPF (rtoc, tox)
