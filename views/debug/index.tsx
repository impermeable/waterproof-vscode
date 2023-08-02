// This is the script that is loaded by Coq's webview

import React from "react";
import { createRoot } from "react-dom/client";

import "../styles/index.css";
// get the react panel
import Debug from "./Debug";

const container = document.getElementById("root");
const root = createRoot(container!); // createRoot(container!) if you use TypeScript
// here we add the react panel, if a panel consists out of a lot of things, 
// consider making them apart and adding them here seperately
root.render(
  <React.StrictMode>
    <Debug/>
  </React.StrictMode>
);
