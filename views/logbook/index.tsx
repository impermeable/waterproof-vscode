// This is the script that is loaded by Coq's webview

import React from "react";
import { createRoot } from "react-dom/client";

import "../styles/index.css";
import Logbook from "./Logbook";

const container = document.getElementById("root");
const root = createRoot(container!); // createRoot(container!) if you use TypeScript
root.render(
  <React.StrictMode>
    <Logbook/>
  </React.StrictMode>
);
